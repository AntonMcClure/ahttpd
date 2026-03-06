#define _GNU_SOURCE
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <signal.h>
#include <errno.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <pwd.h>
#include <grp.h>
#include <dirent.h>
#include <limits.h>
#include <time.h>
#include <sys/utsname.h>
#include <sys/epoll.h>
#include <sys/sendfile.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <bsd/string.h>
#include <openssl/ssl.h>
#include <openssl/err.h>
#include "ver.h"

#define BUF_SIZE 8192
#define MAX_REQUEST_SIZE 8192
#define MAX_REQUEST_LINE 2048
#define MAX_HEADER_COUNT 64

static __thread SSL *client_ssl = NULL;
static __thread int client_fd_g = -1;
static __thread int is_http09 = 0;
static __thread int port = 0;
static int g_http_port = 0;
static int g_https_port = 0;
static __thread char remote_ip[INET_ADDRSTRLEN] = "unknown";
static __thread char g_req_method[16] = "-";
static __thread char g_req_path[1024] = "-";
static __thread char g_req_protocol[16] = "HTTP/1.0";
static __thread int response_status = 200;
static __thread long response_bytes = -1;

static ssize_t client_write(const void *buf, size_t count) {
    if (client_ssl) {
        int ret = SSL_write(client_ssl, buf, (int)count);
        return ret > 0 ? (ssize_t)ret : -1;
    }
    return write(client_fd_g, buf, count);
}

static ssize_t client_write_all(const void *buf, size_t count) {
    const char *p = (const char *)buf;
    size_t remaining = count;
    while (remaining > 0) {
        ssize_t n = client_write(p, remaining);
        if (n <= 0) return -1;
        p += n;
        remaining -= (size_t)n;
    }
    return (ssize_t)count;
}

static ssize_t client_read(void *buf, size_t count) {
    if (client_ssl) {
        int ret = SSL_read(client_ssl, buf, (int)count);
        return ret > 0 ? (ssize_t)ret : -1;
    }
    return read(client_fd_g, buf, count);
}

const char *datetime() {
    static __thread char buffer[64];
    time_t t = time(NULL);
    struct tm tm;
    gmtime_r(&t, &tm);
    strftime(buffer, sizeof(buffer), "%a, %d %b %Y %H:%M:%S GMT", &tm);
    return buffer;
}

static int access_log_fd = -1;
static int error_log_fd = -1;
static pthread_mutex_t log_mutex = PTHREAD_MUTEX_INITIALIZER;

static void open_log_files(void) {
    access_log_fd = open("/var/log/ahttpd/access.log",
                         O_WRONLY | O_APPEND | O_CREAT, 0640);
    error_log_fd = open("/var/log/ahttpd/error.log",
                        O_WRONLY | O_APPEND | O_CREAT, 0640);
}

static void log_access(void) {
    if (access_log_fd < 0) return;
    time_t t = time(NULL);
    struct tm tm_info;
    localtime_r(&t, &tm_info);
    char tsbuf[64];
    strftime(tsbuf, sizeof(tsbuf), "%d/%b/%Y:%H:%M:%S %z", &tm_info);
    char buf[2048];
    int len = snprintf(buf, sizeof(buf), "%s - - [%s] \"%s %s %s\" %d %ld\n",
            remote_ip, tsbuf, g_req_method, g_req_path, g_req_protocol,
            response_status, response_bytes);
    if (len > 0 && (size_t)len < sizeof(buf)) {
        pthread_mutex_lock(&log_mutex);
        ssize_t ret = write(access_log_fd, buf, (size_t)len);
        (void)ret;
        pthread_mutex_unlock(&log_mutex);
    }
}

static void log_error_entry(int code, const char *errmsg) {
    if (error_log_fd < 0) return;
    time_t t = time(NULL);
    struct tm tm_info;
    localtime_r(&t, &tm_info);
    char tsbuf[64];
    strftime(tsbuf, sizeof(tsbuf), "%Y-%m-%d %H:%M:%S", &tm_info);
    char buf[2048];
    int len = snprintf(buf, sizeof(buf), "[%s] [error] [client %s] %d %s: %s\n",
            tsbuf, remote_ip, code, errmsg, g_req_path);
    if (len > 0 && (size_t)len < sizeof(buf)) {
        pthread_mutex_lock(&log_mutex);
        ssize_t ret = write(error_log_fd, buf, (size_t)len);
        (void)ret;
        pthread_mutex_unlock(&log_mutex);
    }
}

typedef struct {
    char *ext;
    char *mime;
} mime_entry;

mime_entry *mime_types = NULL;
size_t mime_count = 0;
size_t mime_capacity = 0;

static int mime_cmp(const void *a, const void *b) {
    return strcasecmp(((const mime_entry *)a)->ext, ((const mime_entry *)b)->ext);
}

void load_mime_types(const char *filename) {
    FILE *fp = fopen(filename, "r");
    if (!fp) return;

    char line[1024];
    while (fgets(line, sizeof(line), fp)) {
        if (line[0] == '#' || strlen(line) < 2) continue;

        char *mime = strtok(line, " \t\n");
        if (!mime) continue;

        char *ext;
        while ((ext = strtok(NULL, " \t\n"))) {
            if (mime_count >= mime_capacity) {
                size_t newcap = mime_capacity ? mime_capacity * 2 : 128;
                mime_entry *newlist = realloc(mime_types, newcap * sizeof(mime_entry));
                if (!newlist) exit(1);
                mime_types = newlist;
                mime_capacity = newcap;
            }
            mime_types[mime_count].ext = strdup(ext);
            mime_types[mime_count].mime = strdup(mime);
            mime_count++;
        }
    }
    fclose(fp);
}

static void load_mime_types_auto(void) {
    static const char *paths[] = {
        "/etc/mime.types",
        "/usr/share/misc/mime.types",
        "/usr/share/mime/types",
        "/usr/local/share/mime/types",
        "/usr/pkg/share/examples/mime-types/mime.types",
        NULL
    };
    for (int i = 0; paths[i]; i++) {
        if (access(paths[i], R_OK) == 0) {
            load_mime_types(paths[i]);
            if (mime_count > 0) {
                qsort(mime_types, mime_count, sizeof(mime_entry), mime_cmp);
                return;
            }
        }
    }
}

void send_redirect(const char *location) {
    char response[BUF_SIZE];
    int len = snprintf(response, sizeof(response),
                       "HTTP/1.0 301 Moved Permanently\r\n"
                       "Server: Aperture/%s\r\n"
                       "Date: %s\r\n"
                       "Location: %s\r\n"
                       "Connection: close\r\n"
                       "Content-Type: text/html\r\n"
                       "X-Clacks-Overhead: GNU Terry Pratchett, J.C. \"Jay Bird\" McClure, Rev. James Berardi, John Falkenstein, Dr. Baffour Takyi, Coco Bean, Rev. Ralph Coletta\r\n"
                       "\r\n",
                       AHTPV, datetime(), location);
    response_status = 301;
    response_bytes = 0;
    if (len > 0) {
        ssize_t ret = client_write_all(response, (size_t)len);
        (void)ret;
    }
}

int is_valid_dns_hostname(const char *host) {
    for (const char *p = host; *p; ++p) {
        if (!isalnum(*p) && *p != '-' && *p != '.') return 0;
    }
    return 1;
}

int is_safe_path(const char *requested_path) {
    char resolved[PATH_MAX];
    if (!realpath(requested_path, resolved)) return 0;
    if (strstr(resolved, "/..") != NULL) return 0;

    struct stat lst;
    if (lstat(requested_path, &lst) == 0 && S_ISLNK(lst.st_mode)) return 0;

    const char *htdocs = "/srv";
    size_t htdocs_len = strlen(htdocs);
    if (strncmp(resolved, htdocs, htdocs_len) == 0 &&
        (resolved[htdocs_len] == '/' || resolved[htdocs_len] == '\0')) return 1;

    const char *docdir = "/usr/share/doc";
    size_t docdir_len = strlen(docdir);
    if (strncmp(resolved, docdir, docdir_len) == 0 &&
        (resolved[docdir_len] == '/' || resolved[docdir_len] == '\0')) return 1;

    const char *home = "/home/";
    size_t home_len = strlen(home);
    if (strncmp(resolved, home, home_len) == 0) {
        const char *after_home = resolved + home_len;
        const char *slash = strchr(after_home, '/');
        if (slash) {
            size_t username_len = (size_t)(slash - after_home);
            char pub_html_prefix[PATH_MAX];
            snprintf(pub_html_prefix, sizeof(pub_html_prefix),
                     "/home/%.*s/www", (int)username_len, after_home);
            size_t prefix_len = strlen(pub_html_prefix);
            if (strncmp(resolved, pub_html_prefix, prefix_len) == 0 &&
                (resolved[prefix_len] == '/' || resolved[prefix_len] == '\0')) return 1;
        }
    }
    return 0;
}

void send_error(int code, const char *errormsg, const char *message, const char *host) {
    response_status = code;
    if (is_http09) return;
    struct utsname name;
    uname(&name);
    char body[BUF_SIZE];
    int body_len = snprintf(body, sizeof(body),
                            "<html><head><title>%d %s</title>\n"
                            "<link rev=\"made\" href=\"mailto:ahttpd@lists.nonpaged.com\">\n"
                            "</head>\n<body>\n<h1>%s</h1>\n%s\n"
                            "<hr><address>Aperture/%s (%s) Server at %s Port %d</address>"
                            "</body></html>",
                            code, errormsg, errormsg, message, AHTPV, name.sysname, host ? host : "localhost", port);

    char header[BUF_SIZE];
    int header_len = snprintf(header, sizeof(header),
                       "HTTP/1.0 %d %s\r\n"
                       "Server: Aperture/%s (%s)\r\n"
                       "Date: %s\r\n"
                       "Content-Length: %d\r\n"
                       "Connection: close\r\n"
                       "Content-Type: text/html\r\n"
                       "X-Clacks-Overhead: GNU Terry Pratchett, J.C. \"Jay Bird\" McClure, Rev. James Berardi, John Falkenstein, Dr. Baffour Takyi, Coco Bean, Rev. Ralph Coletta\r\n"
                       "\r\n",
                       code, errormsg, AHTPV, name.sysname, datetime(), body_len);

    response_bytes = body_len;
    log_error_entry(code, errormsg);
    ssize_t ret = client_write_all(header, (size_t)header_len);
    (void)ret;
    ret = client_write_all(body, (size_t)body_len);
    (void)ret;
}

char *html_escape(const char *input) {
    size_t len = strlen(input);
    size_t outlen = len * 6 + 1;
    char *escaped = malloc(outlen);
    if (!escaped) return NULL;
    size_t pos = 0;
    for (size_t i = 0; i < len; ++i) {
        size_t remaining = outlen - pos;
        int n;
        switch (input[i]) {
            case '&': n = snprintf(escaped + pos, remaining, "&amp;"); break;
            case '<': n = snprintf(escaped + pos, remaining, "&lt;"); break;
            case '>': n = snprintf(escaped + pos, remaining, "&gt;"); break;
            case '"': n = snprintf(escaped + pos, remaining, "&quot;"); break;
            default: escaped[pos++] = input[i]; continue;
        }
        if (n > 0 && (size_t)n < remaining) pos += (size_t)n;
    }
    escaped[pos] = '\0';
    return escaped;
}

static void sanitize_header_value(char *s) {
    for (char *p = s; *p; p++) {
        if (*p == '\r' || *p == '\n') *p = '_';
    }
}

static void make_canonical_path(const char *urlpath, char *out, size_t outsize) {
    if (strnlen(urlpath, outsize) >= outsize) {
        strlcpy(out, "/", outsize);
        return;
    }
    strlcpy(out, urlpath, outsize);

    char *q = strchr(out, '?');
    if (q) *q = '\0';

    const char *last_slash = strrchr(out, '/');
    if (last_slash && last_slash > out) {
        const char *filename = last_slash + 1;
        size_t flen = strlen(filename);

        const char *prev_slash = last_slash - 1;
        while (prev_slash > out && *prev_slash != '/') prev_slash--;
        if (*prev_slash == '/') {
            const char *dirname = prev_slash + 1;
            size_t dirlen = (size_t)(last_slash - prev_slash - 1);

            if (dirlen > 1 && dirname[0] == '~') {
                dirname++;
                dirlen--;
            }

            if (flen == dirlen + 5 &&
                strncmp(filename, dirname, dirlen) == 0 &&
                strcmp(filename + dirlen, ".html") == 0) {
                out[last_slash - out + 1] = '\0';
                return;
            }
            if (flen == dirlen + 4 &&
                strncmp(filename, dirname, dirlen) == 0 &&
                strcmp(filename + dirlen, ".htm") == 0) {
                out[last_slash - out + 1] = '\0';
                return;
            }
        }
    }

    if (strcmp(out, "/home.html") == 0 || strcmp(out, "/home.htm") == 0) {
        strlcpy(out, "/", outsize);
    }
}

typedef struct {
    char *href;
    char *name;
    char *date;
    char *size;
} FileEntry;

static int compare_entries(const void *a, const void *b) {
    const FileEntry *ea = *(const FileEntry **)a;
    const FileEntry *eb = *(const FileEntry **)b;
    int a_is_dir = (strcmp(ea->size, "<dir>") == 0);
    int b_is_dir = (strcmp(eb->size, "<dir>") == 0);
    if (a_is_dir != b_is_dir) return b_is_dir - a_is_dir;
    return strcmp(ea->name, eb->name);
}

void send_directory(const char *dirpath, const char *urlpath, const char *host) {
    DIR *dp = opendir(dirpath);
    if (!dp) {
        send_error(403, "Forbidden", "<p>You are unable to access the directory or file with your provided credentials.</p>", host);
        return;
    }

    struct dirent *ent;
    size_t num_entries = 0;
    size_t capacity = 64;
    FileEntry **file_entries = malloc(capacity * sizeof(FileEntry *));
    if (!file_entries) {
        closedir(dp);
        send_error(500, "Internal Server Error", "<p>Internal server error.</p>", host);
        return;
    }

    size_t max_date_len = strlen("Wednesday, September 30, 2026 12:00 AM");
    size_t max_size_len = strlen("<dir>");

    while ((ent = readdir(dp)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;

        char full_path[PATH_MAX];
        snprintf(full_path, sizeof(full_path), "%s/%s", dirpath, ent->d_name);

        struct stat st;
        if (stat(full_path, &st) < 0) continue;

        FileEntry *entry = malloc(sizeof(FileEntry));
        if (!entry) continue;

        char href[NAME_MAX + 2];
        if (S_ISDIR(st.st_mode)) {
            snprintf(href, sizeof(href), "%s/", ent->d_name);
        } else {
            snprintf(href, sizeof(href), "%s", ent->d_name);
        }
        entry->href = strdup(href);
        entry->name = strdup(ent->d_name);

        char date_buf[64];
        struct tm tm_info;
        gmtime_r(&st.st_mtime, &tm_info);
        strftime(date_buf, sizeof(date_buf), "%A, %B %-d, %Y %l:%M %p", &tm_info);
        entry->date = strdup(date_buf);

        char size_buf[32];
        if (S_ISDIR(st.st_mode)) {
            snprintf(size_buf, sizeof(size_buf), "<dir>");
        } else {
            snprintf(size_buf, sizeof(size_buf), "%ld", (long)st.st_size);
        }
        entry->size = strdup(size_buf);

        if (!entry->href || !entry->name || !entry->date || !entry->size) {
            free(entry->href); free(entry->name); free(entry->date); free(entry->size);
            free(entry);
            continue;
        }

        size_t dlen = strlen(entry->date);
        size_t slen = strlen(entry->size);
        if (dlen > max_date_len) max_date_len = dlen;
        if (slen > max_size_len) max_size_len = slen;

        if (num_entries >= capacity) {
            capacity *= 2;
            FileEntry **tmp = realloc(file_entries, capacity * sizeof(FileEntry *));
            if (!tmp) {
                free(entry->href); free(entry->name); free(entry->date); free(entry->size);
                free(entry);
                continue;
            }
            file_entries = tmp;
        }
        file_entries[num_entries++] = entry;
    }
    closedir(dp);

    qsort(file_entries, num_entries, sizeof(FileEntry *), compare_entries);

    struct utsname uname_buf;
    uname(&uname_buf);

    if (!is_http09) {
        char canonical_path[1024];
        make_canonical_path(urlpath, canonical_path, sizeof(canonical_path));
        sanitize_header_value(canonical_path);

        int is_doc = (strncmp(urlpath, "/doc/", 5) == 0 || strcmp(urlpath, "/doc") == 0);

        char header[BUF_SIZE];
        int header_len = snprintf(header, sizeof(header),
                                  "HTTP/1.0 200 OK\r\n"
                                  "Server: Aperture/%s\r\n"
                                  "Date: %s\r\n"
                                  "Connection: close\r\n"
                                  "Content-Type: text/html\r\n",
                                  AHTPV, datetime());
        if (is_doc)
            header_len += snprintf(header + header_len, sizeof(header) - (size_t)header_len,
                                   "X-Robots-Tag: noindex, nofollow\r\n");
        header_len += snprintf(header + header_len, sizeof(header) - (size_t)header_len,
                               "Link: <https://www.aperture.akron.oh.us%s>; rel=\"canonical\"\r\n"
                               "X-Clacks-Overhead: GNU Terry Pratchett, J.C. \"Jay Bird\" McClure, Rev. James Berardi, John Falkenstein, Dr. Baffour Takyi, Coco Bean, Rev. Ralph Coletta\r\n"
                               "\r\n",
                               canonical_path);
        ssize_t h_ret = client_write_all(header, (size_t)header_len);
        (void)h_ret;
    }
    response_status = 200;

    char chunk[BUF_SIZE];
    int n;
    long total_bytes = 0;

    char *escaped_urlpath = html_escape(urlpath);
    n = snprintf(chunk, sizeof(chunk),
                 "<html><head><title>Index of %s</title></head>\n"
                 "<body><h1>Index of %s</h1>\n<pre>",
                 escaped_urlpath ? escaped_urlpath : urlpath,
                 escaped_urlpath ? escaped_urlpath : urlpath);
    free(escaped_urlpath);
    if (n > 0) { size_t len = (size_t)n < sizeof(chunk) ? (size_t)n : sizeof(chunk) - 1; client_write_all(chunk, len); total_bytes += (long)len; }

    if (strcmp(urlpath, "/") != 0) {
        n = snprintf(chunk, sizeof(chunk),
                     "<a href=\"../\">[To Parent Directory]</a>\n");
        if (n > 0) { size_t len = (size_t)n < sizeof(chunk) ? (size_t)n : sizeof(chunk) - 1; client_write_all(chunk, len); total_bytes += (long)len; }
    }

    for (size_t i = 0; i < num_entries; ++i) {
        FileEntry *curr = file_entries[i];
        char *escaped_href = html_escape(curr->href);
        char *escaped_name = html_escape(curr->name);

        if (strcmp(curr->size, "<dir>") == 0) {
            n = snprintf(chunk, sizeof(chunk),
                         "%*s %10s <a href=\"%s\">%s</a>\n",
                         (int)max_date_len, curr->date,
                         "     &lt;dir&gt;",
                         escaped_href, escaped_name);
        } else {
            n = snprintf(chunk, sizeof(chunk),
                         "%*s %10s <a href=\"%s\">%s</a>\n",
                         (int)max_date_len, curr->date,
                         curr->size,
                         escaped_href, escaped_name);
        }
        if (n > 0) { size_t len = (size_t)n < sizeof(chunk) ? (size_t)n : sizeof(chunk) - 1; client_write_all(chunk, len); total_bytes += (long)len; }

        free(escaped_href);
        free(escaped_name);
        free(curr->href); free(curr->name);
        free(curr->date); free(curr->size);
        free(curr);
    }
    free(file_entries);

    n = snprintf(chunk, sizeof(chunk),
                 "</pre>"
                 "<hr><address>Aperture/%s (%s) Server at %s Port %d</address>"
                 "</body></html>",
                 AHTPV, uname_buf.sysname, host ? host : "localhost", port);
    if (n > 0) { size_t len = (size_t)n < sizeof(chunk) ? (size_t)n : sizeof(chunk) - 1; client_write_all(chunk, len); total_bytes += (long)len; }

    response_bytes = total_bytes;
}

const char *get_mime_type(const char *filename) {
    const char *dot = strrchr(filename, '.');
    if (!dot || dot == filename) return "application/octet-stream";
    dot++;
    mime_entry key = { .ext = (char *)dot, .mime = NULL };
    mime_entry *found = bsearch(&key, mime_types, mime_count,
                                sizeof(mime_entry), mime_cmp);
    if (found) return found->mime;
    return "application/octet-stream";
}

static int ext_in_list(const char *ext, size_t ext_len, const char *list[], size_t list_count) {
    for (size_t i = 0; i < list_count; i++) {
        if (strlen(list[i]) == ext_len && strncasecmp(ext, list[i], ext_len) == 0)
            return 1;
    }
    return 0;
}

static const char *get_forced_type(const char *filename) {
    static const char *plain_exts[] = {
        "txt", "text", "asc", "csv", "tab", "tsv", "log",
        "sig", "gpg", "pgp", "debian", "gz"
    };
    static const char *html_exts[] = {
        "pot", "brf", "srt", "html", "htm", "shtml",
        "xhtml", "mshtml", "mhtml"
    };

    const char *base = strrchr(filename, '/');
    if (base) base++; else base = filename;

    size_t len = strlen(base);
    size_t check_len = len;

    if (check_len > 7 && strncasecmp(base + check_len - 7, ".bak.gz", 7) == 0)
        check_len -= 7;
    else if (check_len > 4 && strncasecmp(base + check_len - 4, ".bak", 4) == 0)
        check_len -= 4;
    else if (check_len > 3 && strncasecmp(base + check_len - 3, ".gz", 3) == 0)
        check_len -= 3;

    const char *dot = NULL;
    for (size_t i = check_len; i > 0; i--) {
        if (base[i - 1] == '.') { dot = base + i; break; }
    }

    /* If no extension found after stripping suffix, try the original name */
    if (!dot) {
        dot = NULL;
        for (size_t i = len; i > 0; i--) {
            if (base[i - 1] == '.') { dot = base + i; break; }
        }
        if (!dot) return NULL;
        check_len = len;
    }

    size_t ext_len = check_len - (size_t)(dot - base);

    if (ext_in_list(dot, ext_len, html_exts, sizeof(html_exts) / sizeof(html_exts[0])))
        return "text/html";
    if (ext_in_list(dot, ext_len, plain_exts, sizeof(plain_exts) / sizeof(plain_exts[0])))
        return "text/plain";
    return NULL;
}

static int file_ends_with_gz(const char *filename) {
    size_t len = strlen(filename);
    return (len > 3 && strcasecmp(filename + len - 3, ".gz") == 0);
}

void send_file(const char *filepath, const char *urlpath, const char *host) {
    int fd = open(filepath, O_RDONLY | O_NOFOLLOW);
    if (fd < 0) {
        send_error(403, "Forbidden", "<p>You are unable to access the directory or file with your provided credentials.</p>", host);
        return;
    }
    struct stat st;
    if (fstat(fd, &st) < 0 || !S_ISREG(st.st_mode)) {
        close(fd);
        send_error(403, "Forbidden", "<p>You are unable to access the directory or file with your provided credentials.</p>", host);
        return;
    }
    if (!is_http09) {
        struct tm tm_info;
        gmtime_r(&st.st_mtime, &tm_info);
        char lastmod[100];
        strftime(lastmod, sizeof(lastmod), "%a, %d %b %Y %H:%M:%S GMT", &tm_info);
        char canonical_path[1024];
        make_canonical_path(urlpath, canonical_path, sizeof(canonical_path));
        sanitize_header_value(canonical_path);

        const char *forced = get_forced_type(filepath);
        const char *content_type = forced ? forced : get_mime_type(filepath);
        int gzip = (forced && file_ends_with_gz(filepath));
        int is_doc = (strncmp(urlpath, "/doc/", 5) == 0 || strcmp(urlpath, "/doc") == 0);

        char header[BUF_SIZE];
        int header_len = snprintf(header, sizeof(header),
                                  "HTTP/1.0 200 OK\r\n"
                                  "Server: Aperture/%s\r\n"
                                  "Date: %s\r\n"
                                  "Last-Modified: %s\r\n"
                                  "Content-Length: %ld\r\n"
                                  "Connection: close\r\n"
                                  "Content-Type: %s\r\n",
                                  AHTPV, datetime(), lastmod, (long)st.st_size,
                                  content_type);
        if (gzip)
            header_len += snprintf(header + header_len, sizeof(header) - (size_t)header_len,
                                   "Content-Encoding: gzip\r\n");
        if (is_doc)
            header_len += snprintf(header + header_len, sizeof(header) - (size_t)header_len,
                                   "X-Robots-Tag: noindex, nofollow\r\n");
        header_len += snprintf(header + header_len, sizeof(header) - (size_t)header_len,
                               "Link: <https://www.aperture.akron.oh.us%s>; rel=\"canonical\"\r\n"
                               "X-Clacks-Overhead: GNU Terry Pratchett, J.C. \"Jay Bird\" McClure, Rev. James Berardi, John Falkenstein, Dr. Baffour Takyi, Coco Bean, Rev. Ralph Coletta\r\n"
                               "\r\n",
                               canonical_path);

        ssize_t h_ret = client_write_all(header, (size_t)header_len);
        (void)h_ret;
    }

    response_status = 200;
    response_bytes = (long)st.st_size;
    if (!client_ssl) {
        off_t offset = 0;
        off_t remaining = st.st_size;
        while (remaining > 0) {
            ssize_t sent = sendfile(client_fd_g, fd, &offset,
                                    (size_t)remaining);
            if (sent > 0) {
                remaining -= sent;
            } else if (sent < 0 && (errno == EINTR || errno == EAGAIN)) {
                continue;
            } else {
                break;
            }
        }
    } else {
        char buf[BUF_SIZE];
        ssize_t n;
        while ((n = read(fd, buf, sizeof(buf))) > 0) {
            ssize_t b_ret = client_write_all(buf, (size_t)n);
            if (b_ret < 0) break;
        }
    }
    close(fd);
}

int daemonize() {
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid > 0) exit(0);

    if (setsid() < 0) exit(1);

    signal(SIGHUP, SIG_IGN);

    pid = fork();
    if (pid < 0) return -1;
    if (pid > 0) exit(0);

    umask(027);
    if (chdir("/") != 0) {}

    close(STDIN_FILENO);
    close(STDOUT_FILENO);
    close(STDERR_FILENO);

    if (open("/dev/null", O_RDONLY) < 0) exit(1);
    if (open("/dev/null", O_WRONLY) < 0) exit(1);
    if (open("/dev/null", O_RDWR) < 0) exit(1);

    return 0;
}

#define MIN_CHILDREN 4
#define MAX_CHILDREN 32
#define THREADS_PER_CHILD 32
#define CONN_TIMEOUT_SEC 30
#define HEADER_TIMEOUT_SEC 10
#define MAX_QUEUE 16384
#define MAX_EVENTS 64
#define MAX_FD_LIMIT 8192

typedef struct {
    int client_fd;
    struct sockaddr_in client_addr;
    int use_ssl;
} conn_task_t;

static conn_task_t task_queue[MAX_QUEUE];
static int queue_head = 0, queue_tail = 0, queue_count = 0;
static pthread_mutex_t queue_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t queue_not_empty = PTHREAD_COND_INITIALIZER;
static SSL_CTX *g_ssl_ctx = NULL;
static int g_use_ssl = 0;

static int get_num_children(void) {
    long ncpus = sysconf(_SC_NPROCESSORS_ONLN);
    if (ncpus < MIN_CHILDREN) ncpus = MIN_CHILDREN;
    if (ncpus > MAX_CHILDREN) ncpus = MAX_CHILDREN;
    return (int)ncpus;
}

static void set_fd_limit(void) {
    struct rlimit rl;
    rl.rlim_cur = MAX_FD_LIMIT;
    rl.rlim_max = MAX_FD_LIMIT;
    if (setrlimit(RLIMIT_NOFILE, &rl) != 0) {
        perror("setrlimit RLIMIT_NOFILE");
    }
}

static volatile sig_atomic_t g_shutdown = 0;
static pid_t *g_children = NULL;
static int g_num_children = 0;

static void sigterm_handler(int sig) {
    (void)sig;
    g_shutdown = 1;
    for (int i = 0; i < g_num_children; i++) {
        if (g_children[i] > 0) {
            kill(g_children[i], SIGTERM);
        }
    }
}

static void sigchld_handler(int sig) {
    (void)sig;
    int saved_errno = errno;
    while (waitpid(-1, NULL, WNOHANG) > 0) {}
    errno = saved_errno;
}

static void drop_privileges(void) {
    if (getuid() != 0) return;

    struct passwd *pw = getpwnam("nobody");
    struct group *gr = getgrnam("nogroup");
    if (!pw || !gr) {
        fprintf(stderr, "Failed to find nobody/nogroup user/group\n");
        _exit(1);
    }

    if (setgid(gr->gr_gid) != 0) {
        perror("setgid");
        _exit(1);
    }
    if (initgroups("nobody", gr->gr_gid) != 0) {
        perror("initgroups");
        _exit(1);
    }
    if (setuid(pw->pw_uid) != 0) {
        perror("setuid");
        _exit(1);
    }

    if (getuid() == 0 || geteuid() == 0) {
        fprintf(stderr, "ERROR: Failed to drop root privileges\n");
        _exit(1);
    }
}

static void handle_client(int client_fd, struct sockaddr_in *client_addr,
                           SSL_CTX *ssl_ctx, int use_ssl) {
    client_ssl = NULL;
    client_fd_g = client_fd;
    is_http09 = 0;
    port = use_ssl ? g_https_port : g_http_port;
    strlcpy(remote_ip, "unknown", sizeof(remote_ip));
    strlcpy(g_req_method, "-", sizeof(g_req_method));
    strlcpy(g_req_path, "-", sizeof(g_req_path));
    strlcpy(g_req_protocol, "HTTP/1.0", sizeof(g_req_protocol));
    response_status = 200;
    response_bytes = -1;

    struct timeval tv = { .tv_sec = CONN_TIMEOUT_SEC, .tv_usec = 0 };
    setsockopt(client_fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    setsockopt(client_fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));

    int nodelay = 1;
    setsockopt(client_fd, IPPROTO_TCP, TCP_NODELAY, &nodelay, sizeof(nodelay));

    inet_ntop(AF_INET, &client_addr->sin_addr, remote_ip, sizeof(remote_ip));

    if (use_ssl) {
        client_ssl = SSL_new(ssl_ctx);
        SSL_set_fd(client_ssl, client_fd);
        if (SSL_accept(client_ssl) <= 0) {
            SSL_free(client_ssl);
            client_ssl = NULL;
            goto cleanup;
        }
    }

    char buffer[MAX_REQUEST_SIZE + 1];
    size_t total_read = 0;
    int headers_complete = 0;
    time_t deadline = time(NULL) + HEADER_TIMEOUT_SEC;

    while (total_read < MAX_REQUEST_SIZE) {
        if (time(NULL) > deadline) goto cleanup;
        ssize_t n = client_read(buffer + total_read,
                                MAX_REQUEST_SIZE - total_read);
        if (n <= 0) goto cleanup;
        total_read += (size_t)n;
        buffer[total_read] = '\0';

        if (strstr(buffer, "\r\n\r\n") != NULL ||
            strstr(buffer, "\n\n") != NULL) {
            headers_complete = 1;
            break;
        }
        if (memchr(buffer, '\n', total_read) != NULL) {
            headers_complete = 1;
            break;
        }
    }

    if (!headers_complete && total_read >= MAX_REQUEST_SIZE) {
        send_error(431, "Request Header Fields Too Large",
                   "<p>The request headers exceed the maximum allowed size.</p>",
                   "localhost");
        goto done;
    }

    char *req_line_end = strstr(buffer, "\r\n");
    size_t req_line_len;
    if (req_line_end) {
        req_line_len = (size_t)(req_line_end - buffer);
    } else {
        char *lf = memchr(buffer, '\n', total_read);
        if (lf) {
            req_line_len = (size_t)(lf - buffer);
        } else {
            req_line_len = total_read;
        }
    }

    if (req_line_len == 0 || req_line_len > MAX_REQUEST_LINE) {
        send_error(400, "Bad Request",
                   "<p>Invalid request line.</p>", "localhost");
        goto done;
    }

    char req_line[MAX_REQUEST_LINE + 1];
    memcpy(req_line, buffer, req_line_len);
    req_line[req_line_len] = '\0';

    char method[16], path[1024], protocol[16];
    is_http09 = 0;

    char *sp1 = strchr(req_line, ' ');
    if (!sp1) {
        send_error(400, "Bad Request",
                   "<p>Invalid request format.</p>", "localhost");
        goto done;
    }

    size_t method_len = (size_t)(sp1 - req_line);
    if (method_len == 0 || method_len >= sizeof(method)) {
        send_error(400, "Bad Request",
                   "<p>Invalid HTTP method.</p>", "localhost");
        goto done;
    }
    memcpy(method, req_line, method_len);
    method[method_len] = '\0';

    for (size_t i = 0; i < method_len; i++) {
        unsigned char c = (unsigned char)method[i];
        if (!isalnum(c) && c != '!' && c != '#' && c != '$' && c != '%' &&
            c != '&' && c != '\'' && c != '*' && c != '+' && c != '-' &&
            c != '.' && c != '^' && c != '_' && c != '`' && c != '|' &&
            c != '~') {
            send_error(400, "Bad Request",
                       "<p>Invalid HTTP method.</p>", "localhost");
            goto done;
        }
    }

    char *uri_start = sp1 + 1;
    while (*uri_start == ' ') uri_start++;
    if (*uri_start == '\0') {
        send_error(400, "Bad Request",
                   "<p>Missing request URI.</p>", "localhost");
        goto done;
    }

    char *sp2 = strchr(uri_start, ' ');
    size_t uri_len;
    if (sp2) {
        uri_len = (size_t)(sp2 - uri_start);
    } else {
        uri_len = strlen(uri_start);
        while (uri_len > 0 && uri_start[uri_len - 1] == ' ')
            uri_len--;
    }

    if (uri_len == 0 || uri_len >= sizeof(path)) {
        send_error(414, "URI Too Long",
                   "<p>The requested URL's length exceeds the capacity limit "
                   "for this server.</p>", "localhost");
        goto done;
    }
    memcpy(path, uri_start, uri_len);
    path[uri_len] = '\0';

    if (path[0] != '/' && path[0] != '*') {
        send_error(400, "Bad Request",
                   "<p>Invalid request URI.</p>", "localhost");
        goto done;
    }

    if (sp2) {
        char *proto_start = sp2 + 1;
        while (*proto_start == ' ') proto_start++;
        size_t proto_len = strlen(proto_start);
        while (proto_len > 0 && proto_start[proto_len - 1] == ' ')
            proto_len--;
        if (proto_len == 0 || proto_len >= sizeof(protocol)) {
            send_error(400, "Bad Request",
                       "<p>Invalid HTTP version.</p>", "localhost");
            goto done;
        }
        memcpy(protocol, proto_start, proto_len);
        protocol[proto_len] = '\0';
        if (proto_len != 8 ||
            strncmp(protocol, "HTTP/", 5) != 0 ||
            !isdigit((unsigned char)protocol[5]) ||
            protocol[6] != '.' ||
            !isdigit((unsigned char)protocol[7])) {
            send_error(400, "Bad Request",
                       "<p>Invalid HTTP version.</p>", "localhost");
            goto done;
        }
    } else {
        is_http09 = 1;
        strlcpy(protocol, "HTTP/0.9", sizeof(protocol));
    }

    strlcpy(g_req_method, method, sizeof(g_req_method));
    strlcpy(g_req_path, path, sizeof(g_req_path));
    strlcpy(g_req_protocol, protocol, sizeof(g_req_protocol));

    if (strcmp(method, "GET") != 0) {
        send_error(501, "Not Implemented", "<p>This server only supports the GET method.</p>", "localhost");
        goto done;
    }

    if (!is_http09) {
        int header_count = 0;
        char *buf_end = buffer + total_read;
        char *hdr_scan = req_line_end ? req_line_end + 2 : NULL;
        if (!hdr_scan) {
            char *lf = strstr(buffer, "\r\n");
            if (lf) {
                hdr_scan = lf + 2;
            } else {
                lf = memchr(buffer, '\n', total_read);
                if (lf) hdr_scan = lf + 1;
            }
        }
        while (hdr_scan && hdr_scan < buf_end && *hdr_scan && *hdr_scan != '\r' && *hdr_scan != '\n') {
            header_count++;
            if (header_count > MAX_HEADER_COUNT) {
                send_error(431, "Request Header Fields Too Large",
                           "<p>Too many request headers.</p>", "localhost");
                goto done;
            }
            char *next = strstr(hdr_scan, "\r\n");
            if (next) {
                hdr_scan = next + 2;
            } else {
                char *nlf = strchr(hdr_scan, '\n');
                if (nlf) hdr_scan = nlf + 1;
                else break;
            }
        }
    }

    char *host = "localhost";
    char host_buf[256];
    if (!is_http09) {
        char *host_header = strstr(buffer, "\r\nHost: ");
        if (!host_header) host_header = strstr(buffer, "\r\nhost: ");
        if (host_header) {
            host_header += 8;
            char *end = strpbrk(host_header, "\r\n:");
            if (end) {
                size_t hlen = (size_t)(end - host_header);
                if (hlen > 0 && hlen < sizeof(host_buf)) {
                    memcpy(host_buf, host_header, hlen);
                    host_buf[hlen] = '\0';
                    if (is_valid_dns_hostname(host_buf)) {
                        host = host_buf;
                    }
                }
            }
        }
    }

    char filepath[PATH_MAX];
    if (path[0] == '/' && path[1] == '~') {
        const char *p = path + 2;
        const char *slash = strchr(p, '/');
        char username[256];
        const char *subpath;
        if (slash) {
            size_t ulen = (size_t)(slash - p);
            if (ulen == 0 || ulen >= sizeof(username)) {
                send_error(400, "Bad Request", "<p>Invalid request.</p>", host);
                goto done;
            }
            memcpy(username, p, ulen);
            username[ulen] = '\0';
            subpath = slash;
        } else {
            strlcpy(username, p, sizeof(username));
            subpath = "/";
        }
        snprintf(filepath, sizeof(filepath), "/home/%s/www%s", username, subpath);
    } else if (strcmp(path, "/doc") == 0 || strncmp(path, "/doc/", 5) == 0) {
        const char *subpath = path + 4;
        if (subpath[0] == '\0')
            snprintf(filepath, sizeof(filepath), "/usr/share/doc");
        else
            snprintf(filepath, sizeof(filepath), "/usr/share/doc%s", subpath);
    } else {
        const char *host_root_dir = "/srv";
        snprintf(filepath, sizeof(filepath), "%s%s", host_root_dir, path);
    }

    char *escaped_path = html_escape(path);
    char err404[2048];
    if (escaped_path) {
        snprintf(err404, sizeof(err404),
                 "<p>The requested URL %s was not found on this server.</p>",
                 escaped_path);
        free(escaped_path);
    } else {
        strlcpy(err404,
                "<p>The requested URL was not found on this server.</p>",
                sizeof(err404));
    }

    if (!is_safe_path(filepath)) {
        send_error(404, "Not Found", err404, host);
    } else {
        struct stat st;
        if (stat(filepath, &st) == 0 && S_ISDIR(st.st_mode)) {
            size_t pathlen = strlen(path);
            if (pathlen == 0 || path[pathlen - 1] != '/') {
                char redirect_loc[PATH_MAX + 2];
                snprintf(redirect_loc, sizeof(redirect_loc), "%s/", path);
                send_redirect(redirect_loc);
            } else {
                const char *dirname = NULL;
                size_t dlen = strlen(path);
                if (dlen > 1 && path[dlen - 1] == '/') dlen--;
                const char *last_sl = path + dlen;
                while (last_sl > path && *(last_sl - 1) != '/') last_sl--;
                size_t dirname_len = (size_t)((path + dlen) - last_sl);
                char dname_buf[256];
                if (dirname_len > 0 && dirname_len < sizeof(dname_buf)) {
                    memcpy(dname_buf, last_sl, dirname_len);
                    dname_buf[dirname_len] = '\0';
                    dirname = dname_buf;
                } else {
                    dirname = "home";
                    dirname_len = 4;
                }
                if (dirname_len > 1 && dirname[0] == '~') {
                    dirname++;
                    dirname_len--;
                }
                char diridx_path[PATH_MAX + 262];
                snprintf(diridx_path, sizeof(diridx_path), "%s%s.html", filepath, dirname);
                if (access(diridx_path, R_OK) == 0) {
                    send_file(diridx_path, path, host);
                } else {
                    snprintf(diridx_path, sizeof(diridx_path), "%s%s.htm", filepath, dirname);
                    if (access(diridx_path, R_OK) == 0) {
                        send_file(diridx_path, path, host);
                    } else {
                        send_directory(filepath, path, host);
                    }
                }
            }
        } else {
            send_file(filepath, path, host);
        }
    }

done:
    log_access();

cleanup:
    if (client_ssl) {
        SSL_shutdown(client_ssl);
        SSL_free(client_ssl);
        client_ssl = NULL;
    }
    close(client_fd);
    client_fd_g = -1;
}

static void *worker_thread(void *arg) {
    (void)arg;
    while (1) {
        conn_task_t task;

        pthread_mutex_lock(&queue_mutex);
        while (queue_count == 0) {
            pthread_cond_wait(&queue_not_empty, &queue_mutex);
        }
        task = task_queue[queue_head];
        queue_head = (queue_head + 1) % MAX_QUEUE;
        queue_count--;
        pthread_mutex_unlock(&queue_mutex);

        handle_client(task.client_fd, &task.client_addr, g_ssl_ctx, task.use_ssl);
    }
    return NULL;
}

static void child_main(int http_fd, int https_fd) {
    pthread_t threads[THREADS_PER_CHILD];
    for (int i = 0; i < THREADS_PER_CHILD; i++) {
        if (pthread_create(&threads[i], NULL, worker_thread, NULL) != 0) {
            _exit(1);
        }
        pthread_detach(threads[i]);
    }

    int epoll_fd = epoll_create1(0);
    if (epoll_fd < 0) _exit(1);

    if (http_fd >= 0) {
        struct epoll_event ev;
        ev.events = EPOLLIN | EPOLLEXCLUSIVE;
        ev.data.fd = http_fd;
        if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, http_fd, &ev) < 0) _exit(1);
    }
    if (https_fd >= 0) {
        struct epoll_event ev;
        ev.events = EPOLLIN | EPOLLEXCLUSIVE;
        ev.data.fd = https_fd;
        if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, https_fd, &ev) < 0) _exit(1);
    }

    struct epoll_event events[MAX_EVENTS];
    while (1) {
        int nfds = epoll_wait(epoll_fd, events, MAX_EVENTS, -1);
        if (nfds < 0) continue;
        for (int i = 0; i < nfds; i++) {
            int ev_fd = events[i].data.fd;
            int is_ssl = (https_fd >= 0 && ev_fd == https_fd);
            struct sockaddr_in client_addr;
            socklen_t addr_len = sizeof(client_addr);
            int client_fd = accept4(ev_fd,
                                    (struct sockaddr *)&client_addr,
                                    &addr_len, SOCK_CLOEXEC);
            if (client_fd < 0) continue;

            pthread_mutex_lock(&queue_mutex);
            if (queue_count >= MAX_QUEUE) {
                close(client_fd);
            } else {
                task_queue[queue_tail].client_fd = client_fd;
                task_queue[queue_tail].client_addr = client_addr;
                task_queue[queue_tail].use_ssl = is_ssl;
                queue_tail = (queue_tail + 1) % MAX_QUEUE;
                queue_count++;
                pthread_cond_signal(&queue_not_empty);
            }
            pthread_mutex_unlock(&queue_mutex);
        }
    }
}

static int create_listen_socket(int listen_port) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
        perror("socket");
        exit(1);
    }

    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &opt, sizeof(opt));

    struct sockaddr_in addr = {
        .sin_family = AF_INET,
        .sin_port = htons(listen_port),
        .sin_addr.s_addr = INADDR_ANY
    };

    if (bind(fd, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
        fprintf(stderr, "Critical: Failed to bind to port %d: %s\n", listen_port, strerror(errno));
        exit(1);
    }

    if (listen(fd, 1024) < 0) {
        perror("listen");
        exit(1);
    }

    return fd;
}

int main(void) {
    struct utsname name;
    const char *cert_file = "/etc/ahttpd/cert.pem";
    const char *key_file = "/etc/ahttpd/key.pem";
    SSL_CTX *ssl_ctx = NULL;
    int use_ssl = 0;

    signal(SIGPIPE, SIG_IGN);

    if (access(cert_file, R_OK) == 0 && access(key_file, R_OK) == 0) {
        use_ssl = 1;

        ssl_ctx = SSL_CTX_new(TLS_server_method());
        if (!ssl_ctx) {
            ERR_print_errors_fp(stderr);
            exit(1);
        }

        if (SSL_CTX_use_certificate_file(ssl_ctx, cert_file, SSL_FILETYPE_PEM) <= 0) {
            ERR_print_errors_fp(stderr);
            exit(1);
        }
        if (SSL_CTX_use_PrivateKey_file(ssl_ctx, key_file, SSL_FILETYPE_PEM) <= 0) {
            ERR_print_errors_fp(stderr);
            exit(1);
        }
        if (!SSL_CTX_check_private_key(ssl_ctx)) {
            fprintf(stderr, "Private key does not match certificate\n");
            exit(1);
        }
    }

    if (uname(&name) == -1) {
        perror("uname error");
        return 1;
    }

    int http_fd = -1;
    int https_fd = -1;

    g_http_port = 80;
    http_fd = create_listen_socket(80);
    if (use_ssl) {
        g_https_port = 443;
        https_fd = create_listen_socket(443);
    }

    set_fd_limit();

    drop_privileges();

    if (daemonize() != 0) {
        perror("daemonize");
        exit(1);
    }

    load_mime_types_auto();
    open_log_files();

    g_ssl_ctx = ssl_ctx;
    g_use_ssl = use_ssl;

    int num_children = get_num_children();

    pid_t *children = calloc((size_t)num_children, sizeof(pid_t));
    if (!children) {
        _exit(1);
    }

    g_children = children;
    g_num_children = num_children;

    struct sigaction sa_term;
    memset(&sa_term, 0, sizeof(sa_term));
    sa_term.sa_handler = sigterm_handler;
    sigemptyset(&sa_term.sa_mask);
    sigaction(SIGTERM, &sa_term, NULL);

    struct sigaction sa_chld;
    memset(&sa_chld, 0, sizeof(sa_chld));
    sa_chld.sa_handler = sigchld_handler;
    sa_chld.sa_flags = SA_NOCLDSTOP;
    sigemptyset(&sa_chld.sa_mask);
    sigaction(SIGCHLD, &sa_chld, NULL);

    for (int i = 0; i < num_children; i++) {
        children[i] = fork();
        if (children[i] < 0) {
            _exit(1);
        }
        if (children[i] == 0) {
            free(children);
            child_main(http_fd, https_fd);
            _exit(0);
        }
    }

    while (!g_shutdown) {
        int status;
        pid_t pid = waitpid(-1, &status, 0);
        if (pid <= 0) continue;
        if (g_shutdown) break;
        for (int i = 0; i < num_children; i++) {
            if (children[i] == pid) {
                children[i] = fork();
                if (children[i] == 0) {
                    free(children);
                    child_main(http_fd, https_fd);
                    _exit(0);
                }
                break;
            }
        }
    }

    for (int i = 0; i < num_children; i++) {
        if (children[i] > 0) {
            waitpid(children[i], NULL, 0);
        }
    }

    free(children);
    if (ssl_ctx) SSL_CTX_free(ssl_ctx);
    return 0;
}
