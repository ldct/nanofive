// Parse each input line (without its newline) as a URL with url.h and print
// what it finds: the url_parse fields, the url_get_* results and a few
// url_get_query_value lookups. url_parse reports a parse error on stderr;
// stdout is unbuffered so the two interleave in the same order everywhere.
#include <stdio.h>
#include <string.h>
#include "url.h"

static void show(const char *name, char *s) {
  printf("  %s: %s%s%s\n", name, s ? "\"" : "", s ? s : "(NULL)", s ? "\"" : "");
  free(s);
}

int main(void) {
  setvbuf(stdout, NULL, _IONBF, 0);
  static char line[1024];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\n")] = '\0';
    printf("%s\n", line);
    url_data_t *u = url_parse(line);
    if (!u) {
      printf("  invalid\n");
      continue;
    }
    url_data_inspect(u);
    static const char *keys[] = {"q", "a", "b", ""};
    for (unsigned i = 0; i < sizeof keys / sizeof keys[0]; i++) {
      const char *v = url_get_query_value(u, keys[i]);
      if (v) printf("  query \"%s\" = \"%s\"\n", keys[i], v);
    }
    printf("  is_protocol: %d, is_ssh: %d\n", url_is_protocol(u->protocol), url_is_ssh(u->protocol));
    url_free(u);
    show("scheme", url_get_scheme(line));
    show("userinfo", url_get_userinfo(line));
    show("hostname", url_get_hostname(line));
    show("port", url_get_port(line));
    show("path", url_get_path(line));
    show("fragment", url_get_fragment(line));
  }
  return 0;
}
