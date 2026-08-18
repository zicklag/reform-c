/* main.c — reform CLI (minimal): load .rf files, then a stdin REPL.
 *
 * Matches the reference CLI's behavior: `$` lines start a buffered
 * multi-line fact (indented lines continue it, a blank line submits it),
 * every other line is a player prompt (wrapped as `> {line}`). */
#include "reform.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  Engine *e = engine_new();
  int rc = 0;
  for (int i = 1; i < argc; i++) {
    if (engine_load_file(e, argv[i])) {
      fprintf(stderr, "%s: error\n", argv[i]);
      rc = 1;
    }
  }

  /* REPL over stdin */
  char *buf = NULL;
  char *line = NULL;
  size_t cap = 0;
  ssize_t n;
  int any_err = 0;
  while ((n = getline(&line, &cap, stdin)) >= 0) {
    if (n && line[n - 1] == '\n')
      line[--n] = 0;
    int i;
    int is_blank = 1;
    for (i = 0; line[i]; i++)
      if (line[i] != ' ' && line[i] != '\t') {
        is_blank = 0;
        break;
      }
    int is_indented = (line[0] == ' ' || line[0] == '\t');

    if (buf) {
      if (is_blank) {
        if (engine_load_str(e, buf)) {
          fprintf(stderr, "error\n");
          any_err = 1;
        }
        free(buf);
        buf = NULL;
      } else if (is_indented) {
        size_t blen = strlen(buf), llen = strlen(line);
        buf = realloc(buf, blen + llen + 2);
        buf[blen] = '\n';
        memcpy(buf + blen + 1, line, llen + 1);
      } else {
        if (engine_load_str(e, buf)) {
          fprintf(stderr, "error\n");
          any_err = 1;
        }
        free(buf);
        buf = NULL;
        if (line[0] == '$') {
          buf = strdup(line);
          continue;
        }
      }
    }
    if (buf == NULL && !is_blank) {
      if (line[0] == '$') {
        buf = strdup(line);
      } else {
        char *p = malloc(n + 4);
        sprintf(p, "> %s", line);
        if (engine_load_str(e, p)) {
          fprintf(stderr, "error\n");
          any_err = 1;
        }
        free(p);
      }
    }
  }
  if (buf) {
    if (engine_load_str(e, buf))
      any_err = 1;
    free(buf);
  }
  free(line);
  engine_free(e);
  return (rc || any_err) ? 1 : 0;
}
