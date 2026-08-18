/* parser.c — facts, patterns, and bodies. Mirrors src/parser.rs peg grammar. */
#include "reform.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* =========================== facts =========================== */

typedef struct {
  const char *s;
  size_t len, pos;
} P;

static bool p_eat(P *p, const char *lit) {
  size_t L = strlen(lit);
  if (p->pos + L <= p->len && memcmp(p->s + p->pos, lit, L) == 0) {
    p->pos += L;
    return true;
  }
  return false;
}
static bool p_at(P *p, const char *lit) {
  size_t L = strlen(lit);
  return p->pos + L <= p->len && memcmp(p->s + p->pos, lit, L) == 0;
}
static bool p_char(P *p, char c) {
  if (p->pos < p->len && p->s[p->pos] == c) {
    p->pos++;
    return true;
  }
  return false;
}
static bool p_eol(P *p) {
  if (p_char(p, '\n'))
    return true;
  return p->pos >= p->len;
}

/* indentation: count leading spaces of current line */
static size_t take_indent(P *p) {
  size_t n = 0;
  while (p->pos < p->len && p->s[p->pos] == ' ') {
    p->pos++;
    n++;
  }
  return n;
}
static bool greater_indent(P *p, size_t base) {
  size_t q = p->pos;
  while (q < p->len && p->s[q] == ' ')
    q++;
  if (q - p->pos > base) {
    p->pos = q;
    return true;
  }
  return false;
}
/* skip a comment to end of line (newline not consumed) */
static void skip_comment(P *p) {
  if (p->pos < p->len && p->s[p->pos] == '#') {
    while (p->pos < p->len && p->s[p->pos] != '\n')
      p->pos++;
  }
}
static bool blank_line(P *p) {
  P q = *p;
  while (q.pos < q.len && (q.s[q.pos] == ' ' || q.s[q.pos] == '\t'))
    q.pos++;
  if (q.pos < q.len && q.s[q.pos] == '\n') {
    p->pos = q.pos + 1;
    return true;
  }
  return false;
}
static bool comment_line(P *p) {
  P q = *p;
  while (q.pos < q.len && (q.s[q.pos] == ' ' || q.s[q.pos] == '\t'))
    q.pos++;
  if (q.pos < q.len && q.s[q.pos] == '#') {
    skip_comment(&q);
    if (q.pos < q.len && q.s[q.pos] == '\n') {
      q.pos++;
      *p = q;
      return true;
    }
    if (q.pos >= q.len) {
      *p = q;
      return true;
    } /* comment to EOF */
    return false;
  }
  return false;
}

/* curly-brace args: { word word } -> {, word, word, } */
static bool curly_args(P *p, U32Arr *out) {
  P q = *p;
  if (!p_eat(&q, "{"))
    return false;
  while (q.pos < q.len && (q.s[q.pos] == ' ' || q.s[q.pos] == '\t'))
    q.pos++;
  U32Arr words = {0};
  while (true) {
    while (q.pos < q.len && (q.s[q.pos] == ' ' || q.s[q.pos] == '\t'))
      q.pos++;
    if (q.pos < q.len && q.s[q.pos] == '}')
      break;
    if (q.pos >= q.len || q.s[q.pos] == '\n') {
      U32Arr_free(&words);
      return false;
    }
    size_t st = q.pos;
    while (q.pos < q.len && q.s[q.pos] != ' ' && q.s[q.pos] != '\t' &&
           q.s[q.pos] != '}' && q.s[q.pos] != '\n')
      q.pos++;
    U32Arr_push(&words, intern(q.s + st, q.pos - st));
  }
  U32Arr_push(out, intern("{", 1));
  for (size_t i = 0; i < words.len; i++)
    U32Arr_push(out, words.data[i]);
  U32Arr_push(out, intern("}", 1));
  U32Arr_free(&words);
  p->pos = q.pos + 1; /* consume } */
  return true;
}

/* single-backtick template interior: chunks merged into args */
typedef struct {
  char *text;
} TmplMerged;
static bool fenced_template(P *p, U32Arr *out);
/* returns args produced by a backtick template (the ` markers + interior args)
 */
static bool backtick_template(P *p, U32Arr *out) {
  /* backtick_template = fenced_template / single_backtick_template */
  if (p_at(p, "```"))
    return fenced_template(p, out);
  P q = *p;
  if (!p_eat(&q, "`"))
    return false;
  U32Arr_push(out, intern("`", 1));
  /* interior: literal text runs (merged) and {curly} substitutions */
  /* We'll collect chunks: text runs and curly sections. Merge consecutive text.
   */
  /* Simpler: build a list of segments. */
  struct Seg {
    enum { S_TEXT, S_CURLY } kind;
    size_t tstart, tlen;
    U32Arr *curly;
  } segs[512];
  size_t nsegs = 0;
  size_t run_start = q.pos; /* start of current text run (inclusive) */
  bool in_run = false;
  while (true) {
    if (q.pos >= q.len)
      return false; /* unterminated */
    if (q.s[q.pos] == '`') {
      if (in_run) {
        segs[nsegs].kind = 0;
        segs[nsegs].tstart = run_start;
        segs[nsegs].tlen = q.pos - run_start;
        nsegs++;
      }
      break;
    }
    /* escapes */
    if (q.s[q.pos] == '\\' && q.pos + 1 < q.len &&
        (q.s[q.pos + 1] == '`' || q.s[q.pos + 1] == '{' ||
         q.s[q.pos + 1] == '}' || q.s[q.pos + 1] == '\\')) {
      if (!in_run) {
        run_start = q.pos;
        in_run = true;
      }
      q.pos += 2; /* treat escape literally; keep as raw text for now, decode
                     later */
      continue;
    }
    if (q.s[q.pos] == '{') {
      if (in_run) {
        segs[nsegs].kind = 0;
        segs[nsegs].tstart = run_start;
        segs[nsegs].tlen = q.pos - run_start;
        nsegs++;
        in_run = false;
      }
      U32Arr ca = {0};
      P cq = q;
      if (curly_args(&cq, &ca)) {
        segs[nsegs].kind = 1;
        segs[nsegs].curly = malloc(sizeof(U32Arr));
        *segs[nsegs].curly = ca;
        nsegs++;
        q = cq;
      } else {
        /* not a valid curly; treat { as text */
        if (!in_run) {
          run_start = q.pos;
          in_run = true;
        }
        q.pos++;
      }
      continue;
    }
    if (!in_run) {
      run_start = q.pos;
      in_run = true;
    }
    q.pos++;
  }
  /* decode text runs with escapes and merge consecutive */
  /* build merged output */
  /* Emit text segments (with escapes decoded) and curly args in order */
  for (size_t i = 0; i < nsegs; i++) {
    if (segs[i].kind == 1) {
      for (size_t j = 0; j < segs[i].curly->len; j++)
        U32Arr_push(out, segs[i].curly->data[j]);
    } else {
      size_t L = segs[i].tlen;
      char *raw = malloc(L + 1);
      memcpy(raw, q.s + segs[i].tstart, L);
      raw[L] = 0;
      /* decode escapes */
      char dec[4096];
      size_t dl = 0;
      for (size_t k = 0; k < L; k++) {
        if (raw[k] == '\\' && k + 1 < L) {
          char nxt = raw[k + 1];
          if (nxt == '`' || nxt == '{' || nxt == '}' || nxt == '\\') {
            dec[dl++] = nxt;
            k++;
            continue;
          }
        }
        dec[dl++] = raw[k];
      }
      dec[dl] = 0;
      U32Arr_push(out, intern(dec, dl));
      free(raw);
    }
  }
  for (size_t i = 0; i < nsegs; i++)
    if (segs[i].kind == 1) {
      free(segs[i].curly);
    }
  p->pos = q.pos + 1; /* consume closing ` */
  U32Arr_push(out, intern("`", 1));
  return true;
}

/* fenced block: ``` ... ``` with dedent. Also produces ` markers. */
static bool fenced_template(P *p, U32Arr *out) {
  P q = *p;
  /* compute column of opening fence (1-based col of `) */
  size_t col = 1;
  for (size_t i = 0; i < q.pos; i++)
    if (q.s[i] == '\n')
      col = 1;
    else
      col++;
  if (!p_eat(&q, "```"))
    return false;
  if (p_char(&q, '\n')) {
  }
  size_t strip = col - 1;
  U32Arr_push(out, intern("`", 1));
  /* gather lines, dedent each by strip, merge text, do curlies */
  /* We'll collect the whole interior as one run with curlies, but dedent per
   * line. */
  struct Seg {
    enum { S_TEXT, S_CURLY } kind;
    size_t tstart, tlen;
    U32Arr *curly;
  } segs[1024];
  size_t nsegs = 0;
  /* process line by line */
  while (true) {
    /* at start of a line (after \n handled). Check for closing fence at current
     * pos. */
    P closeq = q;
    while (closeq.pos < closeq.len &&
           (closeq.s[closeq.pos] == ' ' || closeq.s[closeq.pos] == '\t'))
      closeq.pos++;
    if (closeq.pos + 3 <= closeq.len &&
        memcmp(closeq.s + closeq.pos, "```", 3) == 0) {
      /* closing fence found */
      q = closeq;
      q.pos += 3;
      break;
    }
    /* strip up to `strip` leading spaces */
    size_t stripped = 0;
    while (q.pos < q.len && q.s[q.pos] == ' ' && stripped < strip) {
      q.pos++;
      stripped++;
    }
    /* parse this line's chunks until newline */
    /* add a \n text before continuation lines */
    static int emitted_any = 0;
    (void)emitted_any;
    size_t line_run_start = q.pos;
    bool in_run = false;
    while (q.pos < q.len && q.s[q.pos] != '\n') {
      if (q.s[q.pos] == '{') {
        if (in_run) {
          segs[nsegs].kind = 0;
          segs[nsegs].tstart = line_run_start;
          segs[nsegs].tlen = q.pos - line_run_start;
          nsegs++;
          in_run = false;
        }
        P cq = q;
        U32Arr ca = {0};
        if (curly_args(&cq, &ca)) {
          segs[nsegs].kind = 1;
          segs[nsegs].curly = malloc(sizeof(U32Arr));
          *segs[nsegs].curly = ca;
          nsegs++;
          q = cq;
          continue;
        }
        if (!in_run) {
          line_run_start = q.pos;
          in_run = true;
        }
        q.pos++;
      } else if (q.s[q.pos] == '\\' && q.pos + 1 < q.len &&
                 q.s[q.pos + 1] == '{') {
        if (!in_run) {
          line_run_start = q.pos;
          in_run = true;
        }
        q.pos += 2;
      } else {
        if (!in_run) {
          line_run_start = q.pos;
          in_run = true;
        }
        q.pos++;
      }
    }
    if (in_run) {
      segs[nsegs].kind = 0;
      segs[nsegs].tstart = line_run_start;
      segs[nsegs].tlen = q.pos - line_run_start;
      nsegs++;
    }
    if (q.pos < q.len && q.s[q.pos] == '\n') {
      q.pos++;
      /* add \n text chunk after this line unless next is closing fence */
      /* check closing fence */
      P nx = q;
      while (nx.pos < nx.len && (nx.s[nx.pos] == ' ' || nx.s[nx.pos] == '\t'))
        nx.pos++;
      bool next_close =
          (nx.pos + 3 <= nx.len && memcmp(nx.s + nx.pos, "```", 3) == 0);
      if (!next_close && nsegs) {
        segs[nsegs].kind = 0;
        segs[nsegs].tstart = (size_t)-1;
        segs[nsegs].tlen = 1;
        segs[nsegs].curly = NULL;
        nsegs++; /* newline marker */
      }
    } else
      break;
  }
  /* emit segments in order, merging consecutive text runs into one arg,
   * flushing on each curly section (which emits its args in place) */
  char buf[8192];
  size_t blen = 0;
  for (size_t i = 0; i < nsegs; i++) {
    if (segs[i].kind == 1) {
      if (blen) {
        U32Arr_push(out, intern(buf, blen));
        blen = 0;
      }
      for (size_t j = 0; j < segs[i].curly->len; j++)
        U32Arr_push(out, segs[i].curly->data[j]);
    } else if (segs[i].tstart == (size_t)-1) {
      buf[blen++] = '\n';
    } else {
      size_t L = segs[i].tlen;
      char *raw = malloc(L + 1);
      memcpy(raw, q.s + segs[i].tstart, L);
      raw[L] = 0;
      for (size_t k = 0; k < L; k++) {
        if (raw[k] == '\\' && k + 1 < L &&
            (raw[k + 1] == '{' || raw[k + 1] == '}')) {
          buf[blen++] = raw[k + 1];
          k++;
          continue;
        }
        buf[blen++] = raw[k];
      }
      free(raw);
    }
  }
  if (blen)
    U32Arr_push(out, intern(buf, blen));
  for (size_t i = 0; i < nsegs; i++)
    if (segs[i].kind == 1)
      free(segs[i].curly);
  p->pos = q.pos;
  U32Arr_push(out, intern("`", 1));
  return true;
}

/* literal arg: ( ... ) with escaping and balanced parens, one arg */
static bool literal_arg(P *p, U32Arr *out) {
  P q = *p;
  if (!p_char(&q, '('))
    return false;
  char dec[4096];
  size_t dl = 0;
  while (true) {
    if (q.pos >= q.len)
      return false;
    char c = q.s[q.pos];
    if (c == '\\' && q.pos + 1 < q.len) {
      char nxt = q.s[q.pos + 1];
      if (nxt == '(' || nxt == ')' || nxt == '\\') {
        dec[dl++] = nxt;
        q.pos += 2;
        continue;
      }
      dec[dl++] = c;
      q.pos++;
      continue;
    }
    if (c == '(') { /* nested balanced parens */
      q.pos++;
      char inner[4096];
      size_t il = 0;
      int depth = 1;
      while (q.pos < q.len && depth > 0) {
        char ic = q.s[q.pos];
        if (ic == '(')
          depth++;
        else if (ic == ')') {
          depth--;
          if (depth == 0)
            break;
        }
        inner[il++] = ic;
        q.pos++;
      }
      q.pos++;
      dec[dl++] = '(';
      for (size_t k = 0; k < il; k++)
        dec[dl++] = inner[k];
      dec[dl++] = ')';
      continue;
    }
    if (c == ')') {
      q.pos++;
      break;
    }
    dec[dl++] = c;
    q.pos++;
  }
  dec[dl] = 0;
  U32Arr_push(out, intern(dec, dl));
  p->pos = q.pos;
  return true;
}

/* a plain word or punctuation */
static bool plain_word(P *p, U32Arr *out) {
  P q = *p;
  /* try a word: chars until bracket/comment/space/eol/punct-followed-by-space
   */
  size_t st = q.pos;
  while (q.pos < q.len) {
    char c = q.s[q.pos];
    if (c == '(' || c == ')' || c == '{' || c == '}' || c == '`')
      break;
    if (c == '#')
      break;
    if (c == ' ' || c == '\t' || c == '\n')
      break;
    /* punctuation followed by space/eol */
    if ((c == ',' || c == ';' || c == '.' || c == '\'' || c == ':') &&
        (q.pos + 1 >= q.len || q.s[q.pos + 1] == ' ' ||
         q.s[q.pos + 1] == '\t' || q.s[q.pos + 1] == '\n'))
      break;
    q.pos++;
  }
  if (q.pos > st) {
    U32Arr_push(out, intern(q.s + st, q.pos - st));
    p->pos = q.pos;
    return true;
  }
  /* single punctuation */
  char c = q.s[q.pos];
  if (c == ',' || c == ';' || c == '.' || c == '\'' || c == ':') {
    char t[2] = {c, 0};
    U32Arr_push(out, intern(t, 1));
    q.pos++;
    p->pos = q.pos;
    return true;
  }
  return false;
}

/* args on a single line (a "line_arg_batch" sequence) */
static bool line_args(P *p, U32Arr *out) {
  P q = *p;
  bool any = false;
  while (true) {
    /* skip spaces */
    while (q.pos < q.len && q.s[q.pos] == ' ')
      q.pos++;
    if (q.pos >= q.len || q.s[q.pos] == '\n')
      break;
    /* comment? */
    if (q.s[q.pos] == '#')
      break;
    bool got = backtick_template(&q, out) || curly_args(&q, out) ||
               literal_arg(&q, out) || plain_word(&q, out);
    if (!got)
      break;
    any = true;
  }
  /* trailing comment */
  skip_comment(&q);
  if (!any)
    return false;
  *p = q;
  return true;
}

/* parse a full fact (base indent, first line + continuation lines) */
static bool parse_fact(P *p, Fact *out) {
  P q = *p;
  /* skip sep lines first handled by caller */
  size_t base = take_indent(&q);
  U32Arr args = {0};
  bool ok = line_args(&q, &args);
  if (!ok) {
    U32Arr_free(&args);
    return false;
  }
  /* eol */
  p_eol(&q);
  /* continuation lines */
  while (true) {
    P cq = q;
    /* blank or comment-only at greater indent -> no args */
    P bq = cq;
    if (blank_line(&bq)) {
      q = bq;
      continue;
    }
    P cq2 = cq;
    size_t ind = 0;
    {
      size_t save = cq2.pos;
      while (cq2.pos < cq2.len && cq2.s[cq2.pos] == ' ')
        cq2.pos++;
      ind = cq2.pos - save;
    }
    if (ind > base && cq2.pos < cq2.len && cq2.s[cq2.pos] == '#') {
      skip_comment(&cq2);
      if (cq2.pos < cq2.len && cq2.s[cq2.pos] == '\n') {
        cq2.pos++;
        q = cq2;
        continue;
      }
    }
    /* greater indent then line_args then eol */
    P gq = cq;
    if (greater_indent(&gq, base)) {
      U32Arr more = {0};
      if (line_args(&gq, &more)) {
        p_eol(&gq);
        for (size_t i = 0; i < more.len; i++)
          U32Arr_push(&args, more.data[i]);
        U32Arr_free(&more);
        q = gq;
        continue;
      }
      U32Arr_free(&more);
    }
    break;
  }
  *p = q;
  *out = fact_new(args.data, args.len);
  U32Arr_free(&args);
  return true;
}

int parse_facts(const char *src, FactArr *out) {
  P p = {src, strlen(src), 0};
  /* skip separators */
  while (true) {
    P q = p;
    if (comment_line(&q)) {
      p = q;
      continue;
    }
    if (blank_line(&q)) {
      p = q;
      continue;
    }
    break;
  }
  while (p.pos < p.len) {
    P q = p;
    Fact f;
    if (parse_fact(&q, &f)) {
      FactArr_push(out, f);
      p = q;
    } else {
      /* skip to next newline to avoid infinite loop */
      while (p.pos < p.len && p.s[p.pos] != '\n')
        p.pos++;
      if (p.pos < p.len)
        p.pos++;
    }
    /* skip separators */
    while (true) {
      P qq = p;
      if (comment_line(&qq)) {
        p = qq;
        continue;
      }
      if (blank_line(&qq)) {
        p = qq;
        continue;
      }
      break;
    }
  }
  return 0;
}

/* =========================== patterns =========================== */

/* placeholder name: $ then chars excluding delimiters */
static bool parse_placeholder(P *p, u32 *name_out) {
  P q = *p;
  if (!p_char(&q, '$'))
    return false;
  size_t st = q.pos;
  while (q.pos < q.len) {
    char c = q.s[q.pos];
    if (c == ' ' || c == '\n' || c == '\t' || c == '#' || c == '$' ||
        c == '(' || c == ')' || c == '?' || c == '+' || c == '*' || c == '.' ||
        c == ',' || c == ';' || c == ':' || c == '\'' || c == '!')
      break;
    q.pos++;
  }
  if (q.pos == st)
    return false;
  *name_out = intern(q.s + st, q.pos - st);
  p->pos = q.pos;
  return true;
}

/* repetition marker -> kind, greedy */
static bool parse_rep_marker(P *p, RepKind *kind, bool *greedy) {
  P q = *p;
  if (p_eat(&q, "??")) {
    *kind = RK_OPTIONAL;
    *greedy = true;
    *p = q;
    return true;
  }
  if (p_eat(&q, "++")) {
    *kind = RK_ONEORMORE;
    *greedy = true;
    *p = q;
    return true;
  }
  if (p_eat(&q, "**")) {
    *kind = RK_ZEROORMORE;
    *greedy = true;
    *p = q;
    return true;
  }
  if (p_eat(&q, "?")) {
    *kind = RK_OPTIONAL;
    *greedy = false;
    *p = q;
    return true;
  }
  if (p_eat(&q, "+")) {
    *kind = RK_ONEORMORE;
    *greedy = false;
    *p = q;
    return true;
  }
  if (p_eat(&q, "*")) {
    *kind = RK_ZEROORMORE;
    *greedy = false;
    *p = q;
    return true;
  }
  return false;
}

static bool ws(P *p) {
  while (p->pos < p->len &&
         (p->s[p->pos] == ' ' || p->s[p->pos] == '\t' || p->s[p->pos] == '\n'))
    p->pos++;
  return true;
}

/* literal word in a pattern arg: excludes space \n \t # $ ( ) ? + * ! */
static bool pattern_literal_word(P *p, u32 *out) {
  P q = *p;
  size_t st = q.pos;
  while (q.pos < q.len) {
    char c = q.s[q.pos];
    if (c == ' ' || c == '\n' || c == '\t' || c == '#' || c == '$' ||
        c == '(' || c == ')' || c == '?' || c == '+' || c == '*' || c == '!')
      break;
    q.pos++;
  }
  if (q.pos == st)
    return false;
  *out = intern(q.s + st, q.pos - st);
  p->pos = q.pos;
  return true;
}

/* literal arg in pattern: ( ... ) */
static bool pattern_literal_arg(P *p, u32 *out) {
  P q = *p;
  if (!p_char(&q, '('))
    return false;
  char dec[4096];
  size_t dl = 0;
  while (true) {
    if (q.pos >= q.len)
      return false;
    char c = q.s[q.pos];
    if (c == '\\' && q.pos + 1 < q.len &&
        (q.s[q.pos + 1] == '(' || q.s[q.pos + 1] == ')' ||
         q.s[q.pos + 1] == '\\')) {
      dec[dl++] = q.s[q.pos + 1];
      q.pos += 2;
      continue;
    }
    if (c == ')') {
      q.pos++;
      break;
    }
    dec[dl++] = c;
    q.pos++;
  }
  dec[dl] = 0;
  *out = intern(dec, dl);
  p->pos = q.pos;
  return true;
}

/* arg template: repeated | placeholder | literal_arg | literal_word */
static bool parse_arg_template(P *p, ArgTemplate *out);

/* arg-level repetition: $( ... ) marker  (args multi-line tolerated) */
static bool parse_arg_repetition(P *p, ArgTemplate *out) {
  P q = *p;
  if (!p_eat(&q, "$("))
    return false;
  /* arg_templates_multi: ws() (arg ws())+ ws() */
  ArgTemplate *args = NULL;
  size_t n = 0, cap = 0;
  ws(&q);
  while (true) {
    ArgTemplate a;
    P aq = q;
    if (parse_arg_template(&aq, &a)) {
      if (n == cap) {
        cap = cap ? cap * 2 : 8;
        args = realloc(args, cap * sizeof(ArgTemplate));
      }
      args[n++] = a;
      q = aq;
      ws(&q);
    } else {
      break;
    }
  }
  if (!p_eat(&q, ")")) {
    for (size_t i = 0; i < n; i++)
      at_free(&args[i]);
    free(args);
    return false;
  }
  RepKind kind;
  bool greedy;
  if (!parse_rep_marker(&q, &kind, &greedy)) {
    for (size_t i = 0; i < n; i++)
      at_free(&args[i]);
    free(args);
    return false;
  }
  out->kind = AT_REPEAT;
  out->rep.kind = kind;
  out->rep.greedy = greedy;
  out->rep.args = args;
  out->rep.n = n;
  p->pos = q.pos;
  return true;
}

static bool parse_arg_template(P *p, ArgTemplate *out) {
  P q = *p;
  ArgTemplate a;
  if (parse_arg_repetition(&q, &a)) {
    *out = a;
    p->pos = q.pos;
    return true;
  }
  u32 name;
  if (parse_placeholder(&q, &name)) {
    out->kind = AT_PH;
    out->ph = name;
    p->pos = q.pos;
    return true;
  }
  u32 lit;
  if (pattern_literal_arg(&q, &lit)) {
    out->kind = AT_LIT;
    out->lit = lit;
    p->pos = q.pos;
    return true;
  }
  if (pattern_literal_word(&q, &lit)) {
    out->kind = AT_LIT;
    out->lit = lit;
    p->pos = q.pos;
    return true;
  }
  return false;
}

/* arg_templates on one line: " "* (arg " "*)+ " "*  — with optional comment */
static bool parse_arg_templates_line(P *p, ArgTemplate **out, size_t *outn) {
  P q = *p;
  while (q.pos < q.len && q.s[q.pos] == ' ')
    q.pos++;
  ArgTemplate *args = NULL;
  size_t n = 0, cap = 0;
  bool any = false;
  while (true) {
    while (q.pos < q.len && q.s[q.pos] == ' ')
      q.pos++;
    if (q.pos >= q.len || q.s[q.pos] == '\n')
      break;
    if (q.s[q.pos] == '#')
      break;
    ArgTemplate a;
    P aq = q;
    if (parse_arg_template(&aq, &a)) {
      if (n == cap) {
        cap = cap ? cap * 2 : 8;
        args = realloc(args, cap * sizeof(ArgTemplate));
      }
      args[n++] = a;
      q = aq;
      any = true;
    } else
      break;
  }
  while (q.pos < q.len && q.s[q.pos] == ' ')
    q.pos++;
  skip_comment(&q);
  if (!any) {
    free(args);
    return false;
  }
  *p = q;
  *out = args;
  *outn = n;
  return true;
}

/* pattern fact: take_indent, prefix, arg_templates, comment, fact_end,
 * continuation lines */
static bool parse_pattern_fact_impl(P *p, PatternFact *out) {
  P q = *p;
  size_t base = take_indent(&q);
  bool removed = false, negated = false;
  if (p_char(&q, '-'))
    removed = true;
  else if (p_char(&q, '!'))
    negated = true;
  ArgTemplate *args = NULL;
  size_t n = 0;
  if (!parse_arg_templates_line(&q, &args, &n)) {
    return false;
  }
  /* fact_end: eol or lookahead ) */
  p_eol(&q);
  /* continuation lines: blank/comment no-op, or greater indent + args */
  while (true) {
    P cq = q;
    P bq = cq;
    if (blank_line(&bq)) {
      q = bq;
      continue;
    }
    P cq2 = cq;
    size_t ind = 0;
    {
      size_t save = cq2.pos;
      while (cq2.pos < cq2.len && cq2.s[cq2.pos] == ' ')
        cq2.pos++;
      ind = cq2.pos - save;
    }
    if (ind > base && cq2.pos < cq2.len && cq2.s[cq2.pos] == '#') {
      skip_comment(&cq2);
      if (cq2.pos < cq2.len && cq2.s[cq2.pos] == '\n') {
        cq2.pos++;
        q = cq2;
        continue;
      }
    }
    P gq = cq;
    if (greater_indent(&gq, base)) {
      ArgTemplate *more = NULL;
      size_t mn = 0;
      if (parse_arg_templates_line(&gq, &more, &mn)) {
        p_eol(&gq);
        args = realloc(args, (n + mn) * sizeof(ArgTemplate));
        for (size_t i = 0; i < mn; i++)
          args[n + i] = more[i];
        free(more);
        n += mn;
        q = gq;
        continue;
      }
      free(more);
    }
    break;
  }
  out->removed = removed;
  out->negated = negated;
  out->args = args;
  out->n = n;
  p->pos = q.pos;
  return true;
}

/* pattern: sep* (item sep*)* ws() */
int parse_pattern(const char *src, Pattern *out) {
  P p = {src, strlen(src), 0};
  PatternItem *items = NULL;
  size_t n = 0, cap = 0;
  while (true) {
    P q = p;
    if (comment_line(&q)) {
      p = q;
      continue;
    }
    if (blank_line(&q)) {
      p = q;
      continue;
    }
    break;
  }
  while (p.pos < p.len) {
    P q = p;
    PatternItem it;
    memset(&it, 0, sizeof(it));
    /* try fact repetition: " "* "$(" ... */
    P rq = q;
    while (rq.pos < rq.len && (rq.s[rq.pos] == ' ' || rq.s[rq.pos] == '\t'))
      rq.pos++;
    if (rq.pos + 2 <= rq.len && memcmp(rq.s + rq.pos, "$(", 2) == 0) {
      /* pattern_fact_repetition */
      P fq = rq;
      fq.pos += 2;
      while (fq.pos < fq.len && (fq.s[fq.pos] == ' ' || fq.s[fq.pos] == '\t'))
        fq.pos++;
      skip_comment(&fq);
      p_eol(&fq);
      while (true) {
        P cq = fq;
        if (comment_line(&cq)) {
          fq = cq;
          continue;
        }
        if (blank_line(&cq)) {
          fq = cq;
          continue;
        }
        break;
      }
      PatternFact *facts = NULL;
      size_t fn = 0, fcap = 0;
      while (true) {
        PatternFact pf;
        P pfq = fq;
        if (parse_pattern_fact_impl(&pfq, &pf)) {
          if (fn == fcap) {
            fcap = fcap ? fcap * 2 : 4;
            facts = realloc(facts, fcap * sizeof(PatternFact));
          }
          facts[fn++] = pf;
          fq = pfq;
          while (true) {
            P cq = fq;
            if (comment_line(&cq)) {
              fq = cq;
              continue;
            }
            if (blank_line(&cq)) {
              fq = cq;
              continue;
            }
            break;
          }
        } else {
          break;
        }
      }
      /* ws() ")" marker */
      ws(&fq);
      if (!p_char(&fq, ')')) {
        for (size_t i = 0; i < fn; i++)
          pf_free(&facts[i]);
        free(facts);
        return -1;
      }
      RepKind kind;
      bool greedy;
      if (!parse_rep_marker(&fq, &kind, &greedy)) {
        for (size_t i = 0; i < fn; i++)
          pf_free(&facts[i]);
        free(facts);
        return -1;
      }
      while (fq.pos < fq.len && (fq.s[fq.pos] == ' ' || fq.s[fq.pos] == '\t'))
        fq.pos++;
      skip_comment(&fq);
      p_eol(&fq);
      it.kind = PI_FACTREP;
      it.rep.kind = kind;
      it.rep.greedy = greedy;
      it.rep.facts = facts;
      it.rep.n = fn;
      q = fq;
    } else {
      PatternFact pf;
      if (!parse_pattern_fact_impl(&q, &pf))
        break;
      it.kind = PI_FACT;
      it.fact = pf;
    }
    if (n == cap) {
      cap = cap ? cap * 2 : 8;
      items = realloc(items, cap * sizeof(PatternItem));
    }
    items[n++] = it;
    p = q;
    while (true) {
      P cq = p;
      if (comment_line(&cq)) {
        p = cq;
        continue;
      }
      if (blank_line(&cq)) {
        p = cq;
        continue;
      }
      break;
    }
  }
  out->items = items;
  out->n = n;
  return 0;
}

int parse_pattern_fact(const char *src, PatternFact *out) {
  P p = {src, strlen(src), 0};
  return parse_pattern_fact_impl(&p, out) ? 0 : -1;
}

/* =========================== bodies =========================== */

static bool body_chunk_in_repeat(P *p, BodyChunk *out);
static bool body_chunk(P *p, BodyChunk *out);

static bool body_chunk(P *p, BodyChunk *out) {
  P q = *p;
  if (p_eat(&q, "$$")) {
    out->kind = BC_TEXT;
    out->text = strdup("$");
    p->pos = q.pos;
    return true;
  }
  if (p_eat(&q, "$(")) {
    BodyChunk *chunks = NULL;
    size_t n = 0, cap = 0;
    while (true) {
      P cq = q;
      BodyChunk c;
      if (body_chunk_in_repeat(&cq, &c)) {
        if (n == cap) {
          cap = cap ? cap * 2 : 8;
          chunks = realloc(chunks, cap * sizeof(BodyChunk));
        }
        chunks[n++] = c;
        q = cq;
      } else
        break;
    }
    if (!p_eat(&q, ")")) {
      for (size_t i = 0; i < n; i++)
        bc_free(&chunks[i]);
      free(chunks);
      p->pos = q.pos;
      out->kind = BC_TEXT;
      out->text = strdup("$(");
      return true;
    }
    RepKind kind;
    bool greedy;
    if (!parse_rep_marker(&q, &kind, &greedy)) {
      for (size_t i = 0; i < n; i++)
        bc_free(&chunks[i]);
      free(chunks);
      p->pos = q.pos;
      out->kind = BC_TEXT;
      out->text = strdup("$(");
      return true;
    }
    out->kind = BC_REPEAT;
    out->rep.kind = kind;
    out->rep.greedy = greedy;
    out->rep.chunks = chunks;
    out->rep.n = n;
    p->pos = q.pos;
    return true;
  }
  u32 name;
  if (parse_placeholder(&q, &name)) {
    out->kind = BC_PH;
    out->ph = name;
    p->pos = q.pos;
    return true;
  }
  if (p_char(&q, '$')) {
    out->kind = BC_TEXT;
    out->text = strdup("$");
    p->pos = q.pos;
    return true;
  }
  size_t st = q.pos;
  while (q.pos < q.len && q.s[q.pos] != '$')
    q.pos++;
  if (q.pos == st)
    return false;
  out->kind = BC_TEXT;
  out->text = malloc(q.pos - st + 1);
  memcpy(out->text, q.s + st, q.pos - st);
  out->text[q.pos - st] = 0;
  p->pos = q.pos;
  return true;
}

/* chunk inside a repeat: `)` closes only when followed by rep marker */
static bool body_chunk_in_repeat(P *p, BodyChunk *out) {
  P q = *p;
  if (p_eat(&q, "$$")) {
    out->kind = BC_TEXT;
    out->text = strdup("$");
    p->pos = q.pos;
    return true;
  }
  if (p_eat(&q, "$(")) {
    BodyChunk *chunks = NULL;
    size_t n = 0, cap = 0;
    while (true) {
      P cq = q;
      BodyChunk c;
      if (body_chunk_in_repeat(&cq, &c)) {
        if (n == cap) {
          cap = cap ? cap * 2 : 8;
          chunks = realloc(chunks, cap * sizeof(BodyChunk));
        }
        chunks[n++] = c;
        q = cq;
      } else
        break;
    }
    if (!p_eat(&q, ")")) {
      for (size_t i = 0; i < n; i++)
        bc_free(&chunks[i]);
      free(chunks);
      p->pos = q.pos;
      out->kind = BC_TEXT;
      out->text = strdup("$(");
      return true;
    }
    RepKind kind;
    bool greedy;
    if (!parse_rep_marker(&q, &kind, &greedy)) {
      for (size_t i = 0; i < n; i++)
        bc_free(&chunks[i]);
      free(chunks);
      p->pos = q.pos;
      out->kind = BC_TEXT;
      out->text = strdup("$(");
      return true;
    }
    out->kind = BC_REPEAT;
    out->rep.kind = kind;
    out->rep.greedy = greedy;
    out->rep.chunks = chunks;
    out->rep.n = n;
    p->pos = q.pos;
    return true;
  }
  u32 name;
  if (parse_placeholder(&q, &name)) {
    out->kind = BC_PH;
    out->ph = name;
    p->pos = q.pos;
    return true;
  }
  if (p_char(&q, '$')) {
    out->kind = BC_TEXT;
    out->text = strdup("$");
    p->pos = q.pos;
    return true;
  }
  /* text: either !")" !"$" [_]  or  ")" !rep_marker */
  size_t st = q.pos;
  while (q.pos < q.len) {
    char c = q.s[q.pos];
    if (c == '$')
      break;
    if (c == ')') {
      /* closes only if followed by rep marker */
      RepKind k;
      bool g;
      P rq = q;
      rq.pos++;
      if (parse_rep_marker(&rq, &k, &g))
        break; /* this ) ends the repeat */
      q.pos++;
      continue;
    }
    q.pos++;
  }
  if (q.pos == st)
    return false;
  out->kind = BC_TEXT;
  out->text = malloc(q.pos - st + 1);
  memcpy(out->text, q.s + st, q.pos - st);
  out->text[q.pos - st] = 0;
  p->pos = q.pos;
  return true;
}

void parse_body(const char *src, Body *out) {
  P p = {src, strlen(src), 0};
  BodyChunk *chunks = NULL;
  size_t n = 0, cap = 0;
  while (p.pos < p.len) {
    BodyChunk c;
    if (body_chunk(&p, &c)) {
      if (n == cap) {
        cap = cap ? cap * 2 : 8;
        chunks = realloc(chunks, cap * sizeof(BodyChunk));
      }
      chunks[n++] = c;
    } else
      break;
  }
  /* merge adjacent text chunks */
  BodyChunk *merged = NULL;
  size_t mn = 0;
  for (size_t i = 0; i < n; i++) {
    if (chunks[i].kind == BC_TEXT && mn && merged[mn - 1].kind == BC_TEXT) {
      size_t a = strlen(merged[mn - 1].text), b = strlen(chunks[i].text);
      merged[mn - 1].text = realloc(merged[mn - 1].text, a + b + 1);
      memcpy(merged[mn - 1].text + a, chunks[i].text, b + 1);
      bc_free(&chunks[i]);
    } else {
      merged = realloc(merged, (mn + 1) * sizeof(BodyChunk));
      merged[mn++] = chunks[i];
    }
  }
  free(chunks);
  out->chunks = merged;
  out->n = mn;
}
