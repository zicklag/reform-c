/* engine.c — rule engine: fixpoint loop, specificity, body rendering, commands.
 */
#include "reform.h"
#include <ctype.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int ingest_body(Engine *e, Fact *fact);

/* specificity */
static u64 rep_penalty(RepKind k) {
  return k == RK_OPTIONAL ? 1 : k == RK_ONEORMORE ? 3 : 4;
}
static u64 arg_spec(const ArgTemplate *a, u64 penalty) {
  switch (a->kind) {
  case AT_LIT:
    return 5 > penalty ? 5 - penalty : 0;
  case AT_PH:
    return 4 > penalty ? 4 - penalty : 0;
  case AT_REPEAT: {
    u64 p = penalty + rep_penalty(a->rep.kind);
    u64 s = 0;
    for (size_t i = 0; i < a->rep.n; i++)
      s += arg_spec(&a->rep.args[i], p);
    return s;
  }
  default:
    return 0;
  }
}
static u64 fact_score(const PatternFact *pf, u64 penalty) {
  if (pf->negated)
    return 0;
  u64 s = 1;
  for (size_t i = 0; i < pf->n; i++)
    s += arg_spec(&pf->args[i], penalty);
  return s;
}
static u64 pattern_spec(const Pattern *p) {
  u64 s = 0;
  for (size_t i = 0; i < p->n; i++) {
    if (p->items[i].kind == PI_FACT)
      s += fact_score(&p->items[i].fact, 0);
    else {
      u64 pen = rep_penalty(p->items[i].rep.kind);
      for (size_t f = 0; f < p->items[i].rep.n; f++)
        s += fact_score(&p->items[i].rep.facts[f], pen);
    }
  }
  return s;
}

/* body rendering */
static void render_value(const BindValue *v, char **out);
static void render_chunks(const BodyChunk *chunks, size_t n, const Bindings *b,
                          char **out);
static void collect_body_ph(const BodyChunk *chunks, size_t n, U32Arr *out);

static void render_value(const BindValue *v, char **out) {
  if (v->kind == BV_ONE) {
    const char *s = normal_form_arg(v->one);
    size_t L = strlen(s), o = strlen(*out);
    *out = realloc(*out, o + L + 1);
    memcpy(*out + o, s, L);
    (*out)[o + L] = 0;
  } else {
    for (size_t i = 0; i < v->many.len; i++) {
      if (i) {
        size_t o = strlen(*out);
        *out = realloc(*out, o + 2);
        (*out)[o] = ' ';
        (*out)[o + 1] = 0;
      }
      render_value(&v->many.items[i], out);
    }
  }
}
static void collect_body_ph(const BodyChunk *chunks, size_t n, U32Arr *out) {
  for (size_t i = 0; i < n; i++) {
    if (chunks[i].kind == BC_PH)
      U32Arr_push(out, chunks[i].ph);
    else if (chunks[i].kind == BC_REPEAT)
      collect_body_ph(chunks[i].rep.chunks, chunks[i].rep.n, out);
  }
}
static void render_repeat(const BodyChunk *r, const Bindings *b, char **out) {
  U32Arr phs = {0};
  collect_body_ph(r->rep.chunks, r->rep.n, &phs);
  /* driver lists: each ph that is a Many */
  size_t nd = 0;
  u32 *dnames = NULL;
  BindValue **dlists = NULL;
  size_t n = 0;
  for (size_t i = 0; i < phs.len; i++) {
    BindValue *v = bing_get((Bindings *)b, phs.data[i]);
    if (v && v->kind == BV_MANY) {
      dnames = realloc(dnames, (nd + 1) * sizeof(u32));
      dnames[nd] = phs.data[i];
      dlists = realloc(dlists, (nd + 1) * sizeof(BindValue *));
      dlists[nd] = v;
      nd++;
      n = v->many.len;
    }
  }
  U32Arr_free(&phs);
  if (!nd)
    return;
  for (size_t i = 0; i < nd; i++)
    if (dlists[i]->many.len != n)
      return;
  for (size_t i = 0; i < n; i++) {
    Bindings b2 = *b;
    b2.names = NULL;
    b2.vals = NULL;
    b2.len = b2.cap = 0;
    for (size_t k = 0; k < b->len; k++) {
      const BindValue *v = &b->vals[k];
      if (v->kind == BV_ONE)
        bing_bind_scalar(&b2, b->names[k], v->one);
      else {
        BindValue nv;
        nv.kind = BV_MANY;
        nv.many.items = NULL;
        nv.many.len = nv.many.cap = 0;
        for (size_t m = 0; m < v->many.len; m++) {
          bv_push(&nv, v->many.items[m]);
        }
        bing_set_into(&b2, b->names[k], nv);
      }
    }
    for (size_t d = 0; d < nd; d++) {
      /* replace with list[i] */
      for (size_t k = 0; k < b2.len; k++)
        if (b2.names[k] == dnames[d]) {
          bv_free(&b2.vals[k]);
          b2.vals[k] = dlists[d]->many.items[i];
          break;
        }
    }
    render_chunks(r->rep.chunks, r->rep.n, &b2, out);
    /* free b2 but not the transferred values (they're shared) */
    free(b2.names);
    free(b2.vals);
  }
  free(dnames);
  free(dlists);
}
static void render_chunks(const BodyChunk *chunks, size_t n, const Bindings *b,
                          char **out) {
  for (size_t i = 0; i < n; i++) {
    const BodyChunk *c = &chunks[i];
    if (c->kind == BC_TEXT) {
      size_t L = strlen(c->text), o = strlen(*out);
      *out = realloc(*out, o + L + 1);
      memcpy(*out + o, c->text, L);
      (*out)[o + L] = 0;
    } else if (c->kind == BC_PH) {
      BindValue *v = bing_get((Bindings *)b, c->ph);
      if (v)
        render_value(v, out);
    } else {
      render_repeat(c, b, out);
    }
  }
}

/* engine */
struct Engine {
  FactArr facts;
  /* rules: name, specificity, pattern, body */
  u32 *names;
  i64 *specs;
  Pattern *pats;
  Body *bodies;
  size_t nrules;
  bool quit;
  size_t max_iterations;
  char *base_dir;
  Sink stdout, stderr;
  u64 rng_state;
  bool trace;
};

static Bindings *bing0(void);

Engine *engine_new(void) {
  Engine *e = calloc(1, sizeof(Engine));
  e->facts.data = NULL;
  e->facts.len = e->facts.cap = 0;
  e->max_iterations = 100000;
  e->stdout = NULL;
  e->stderr = NULL;
  e->rng_state = 0x9E3779B97F4A7C15;
  return e;
}
void engine_free(Engine *e) {
  FactArr_free(&e->facts);
  for (size_t i = 0; i < e->nrules; i++) {
    pattern_free(&e->pats[i]);
    body_free(&e->bodies[i]);
  }
  free(e->names);
  free(e->specs);
  free(e->pats);
  free(e->bodies);
  free(e->base_dir);
  free(e);
}
void engine_set_base_dir(Engine *e, const char *path) {
  free(e->base_dir);
  e->base_dir = path ? strdup(path) : NULL;
}
void engine_set_stdout(Engine *e, Sink s) { e->stdout = s; }
void engine_set_stderr(Engine *e, Sink s) { e->stderr = s; }
int engine_set_seed(Engine *e, u64 seed) {
  e->rng_state = seed;
  return 0;
}
static void out_s(Engine *e, const char *s) {
  if (e->stdout)
    e->stdout(s);
  else
    fputs(s, stdout);
}
static void err_s(Engine *e, const char *s) {
  if (e->stderr)
    e->stderr(s);
  else
    fputs(s, stderr);
}

static bool add_fact(Engine *e, Fact *f) {
  for (size_t i = 0; i < e->facts.len; i++)
    if (fact_eq(&e->facts.data[i], f))
      return false;
  FactArr_push(&e->facts, *f);
  return true;
}
static bool remove_fact(Engine *e, const Fact *f) {
  for (size_t i = 0; i < e->facts.len; i++)
    if (fact_eq(&e->facts.data[i], f)) {
      /* capture before freeing the fact (fact_is_rule/resolve read f->args) */
      bool is_rule = fact_is_rule(f);
      u32 rule_name = is_rule ? f->args[1] : 0;
      fact_free(&e->facts.data[i]);
      memmove(&e->facts.data[i], &e->facts.data[i + 1],
              (e->facts.len - i - 1) * sizeof(Fact));
      e->facts.len--;
      if (is_rule) {
        const char *nm = resolve(rule_name);
        for (size_t r = 0; r < e->nrules; r++)
          if (strcmp(resolve(e->names[r]), nm) == 0) {
            pattern_free(&e->pats[r]);
            body_free(&e->bodies[r]);
            memmove(&e->names[r], &e->names[r + 1],
                    (e->nrules - r - 1) * sizeof(u32));
            memmove(&e->specs[r], &e->specs[r + 1],
                    (e->nrules - r - 1) * sizeof(i64));
            memmove(&e->pats[r], &e->pats[r + 1],
                    (e->nrules - r - 1) * sizeof(Pattern));
            memmove(&e->bodies[r], &e->bodies[r + 1],
                    (e->nrules - r - 1) * sizeof(Body));
            e->nrules--;
            break;
          }
      }
      return true;
    }
  return false;
}

/* add a rule, sort by specificity descending (stable by insertion) */
static void add_rule(Engine *e, u32 name, i64 spec, Pattern pat, Body body) {
  e->names = realloc(e->names, (e->nrules + 1) * sizeof(u32));
  e->specs = realloc(e->specs, (e->nrules + 1) * sizeof(i64));
  e->pats = realloc(e->pats, (e->nrules + 1) * sizeof(Pattern));
  e->bodies = realloc(e->bodies, (e->nrules + 1) * sizeof(Body));
  e->names[e->nrules] = name;
  e->specs[e->nrules] = spec;
  e->pats[e->nrules] = pat;
  e->bodies[e->nrules] = body;
  e->nrules++;
  /* insertion sort stable by spec desc */
  for (size_t i = e->nrules; i > 1 && e->specs[i - 1] > e->specs[i - 2]; i--) {
    u32 tn = e->names[i - 1];
    e->names[i - 1] = e->names[i - 2];
    e->names[i - 2] = tn;
    i64 ts = e->specs[i - 1];
    e->specs[i - 1] = e->specs[i - 2];
    e->specs[i - 2] = ts;
    Pattern tp = e->pats[i - 1];
    e->pats[i - 1] = e->pats[i - 2];
    e->pats[i - 2] = tp;
    Body tb = e->bodies[i - 1];
    e->bodies[i - 1] = e->bodies[i - 2];
    e->bodies[i - 2] = tb;
  }
}

/* @eval: parse and evaluate a simple f64 arithmetic expression (meval subset)
 */
/* We use a tiny recursive-descent evaluator over a string. */
typedef struct {
  const char *s;
  size_t len, pos;
  double rng;
} EV;
static double eval_expr(EV *e);
static double eval_term(EV *e);
static double eval_pow(EV *e);
static double eval_unary(EV *e);
static double eval_factor(EV *e);
static void ev_ws(EV *e) {
  while (e->pos < e->len && (e->s[e->pos] == ' ' || e->s[e->pos] == '\t'))
    e->pos++;
}
static bool ev_num(EV *e, double *out) {
  ev_ws(e);
  char buf[64];
  size_t n = 0;
  if (e->pos < e->len && (e->s[e->pos] == '+' || e->s[e->pos] == '-'))
    buf[n++] = e->s[e->pos++];
  while (e->pos < e->len &&
         (isdigit((unsigned char)e->s[e->pos]) || e->s[e->pos] == '.' ||
          e->s[e->pos] == 'e' || e->s[e->pos] == 'E' || e->s[e->pos] == '-')) {
    if (n < 63)
      buf[n++] = e->s[e->pos++];
    else
      e->pos++;
  }
  /* don't swallow binary '-' after an 'e' as sign is fine; this is crude */
  if (n) {
    buf[n] = 0;
    *out = strtod(buf, NULL);
    return true;
  }
  return false;
}
static double eval_factor(EV *e) {
  ev_ws(e);
  if (e->pos < e->len && e->s[e->pos] == '(') {
    e->pos++;
    double v = eval_expr(e);
    ev_ws(e);
    if (e->pos < e->len && e->s[e->pos] == ')')
      e->pos++;
    return v;
  }
  /* function call */
  if (e->pos < e->len && isalpha((unsigned char)e->s[e->pos])) {
    char fn[32];
    size_t n = 0;
    while (e->pos < e->len && isalpha((unsigned char)e->s[e->pos]) && n < 31)
      fn[n++] = e->s[e->pos++];
    fn[n] = 0;
    ev_ws(e);
    if (e->pos < e->len && e->s[e->pos] == '(') {
      e->pos++;
      double arg = eval_expr(e);
      ev_ws(e);
      if (e->pos < e->len && e->s[e->pos] == ')')
        e->pos++;
      if (strcmp(fn, "sqrt") == 0)
        return sqrt(arg);
      if (strcmp(fn, "abs") == 0)
        return fabs(arg);
      if (strcmp(fn, "sin") == 0)
        return sin(arg);
      if (strcmp(fn, "cos") == 0)
        return cos(arg);
      if (strcmp(fn, "floor") == 0)
        return floor(arg);
      if (strcmp(fn, "ceil") == 0)
        return ceil(arg);
      if (strcmp(fn, "random") == 0)
        return e->rng * arg; /* crude */
      return arg;
    }
    return 0;
  }
  double v;
  if (ev_num(e, &v))
    return v;
  return 0;
}
static double eval_unary(EV *e) {
  ev_ws(e);
  if (e->pos < e->len && (e->s[e->pos] == '-' || e->s[e->pos] == '+')) {
    char op = e->s[e->pos++];
    double v = eval_unary(e);
    return op == '-' ? -v : v;
  }
  return eval_factor(e);
}
static double eval_pow(EV *e) {
  double l = eval_unary(e);
  ev_ws(e);
  if (e->pos < e->len && e->s[e->pos] == '^') {
    e->pos++;
    double r = eval_pow(e);
    return pow(l, r);
  }
  return l;
}
static double eval_term(EV *e) {
  double l = eval_pow(e);
  ev_ws(e);
  while (e->pos < e->len && (e->s[e->pos] == '*' || e->s[e->pos] == '/')) {
    char op = e->s[e->pos++];
    double r = eval_pow(e);
    l = op == '*' ? l * r : l / r;
    ev_ws(e);
  }
  return l;
}
static double eval_expr(EV *e) {
  double l = eval_term(e);
  ev_ws(e);
  while (e->pos < e->len && (e->s[e->pos] == '+' || e->s[e->pos] == '-')) {
    char op = e->s[e->pos++];
    double r = eval_term(e);
    l = op == '+' ? l + r : l - r;
    ev_ws(e);
  }
  return l;
}

/* @eval reduction: replace "@eval" <expr> with the evaluated string in a fact
 */
static void reduce_evals(Engine *e, Fact *f) {
  u32 *out = NULL;
  size_t on = 0, ocap = 0;
  size_t i = 0;
  while (i < f->len) {
    const char *s = resolve(f->args[i]);
    bool is_eval = strlen(s) == 5 && memcmp(s, "@eval", 5) == 0;
    if (is_eval && i + 1 < f->len) {
      EV ev = {resolve(f->args[i + 1]), strlen(resolve(f->args[i + 1])), 0, 0};
      double v = eval_expr(&ev);
      if (ev.pos >= ev.len) { /* fully parsed */
        char buf[64];
        if (v == (long long)v && fabs(v) < 1e15)
          snprintf(buf, sizeof(buf), "%lld", (long long)v);
        else
          snprintf(buf, sizeof(buf), "%.15g", v);
        if (on == ocap) {
          ocap = ocap ? ocap * 2 : 8;
          out = realloc(out, ocap * sizeof(u32));
        }
        out[on++] = intern(buf, strlen(buf));
        i += 2;
        continue;
      }
    }
    if (on == ocap) {
      ocap = ocap ? ocap * 2 : 8;
      out = realloc(out, ocap * sizeof(u32));
    }
    out[on++] = f->args[i];
    i++;
  }
  free(f->args);
  f->args = out;
  f->len = on;
}

bool engine_contains(Engine *e, const Fact *f) {
  for (size_t i = 0; i < e->facts.len; i++)
    if (fact_eq(&e->facts.data[i], f))
      return true;
  return false;
}

/* command dispatch: return 0 ok, -1 error (message printed to stderr) */
static int dispatch_command(Engine *e, const char *name, const u32 *args,
                            size_t n) {
  if (strcmp(name, "println") == 0) {
    size_t total = 0;
    for (size_t i = 0; i < n; i++)
      total += strlen(resolve(args[i]));
    char *buf = malloc(total + 2);
    size_t o = 0;
    for (size_t i = 0; i < n; i++) {
      const char *s = resolve(args[i]);
      size_t L = strlen(s);
      memcpy(buf + o, s, L);
      o += L;
    }
    buf[o] = '\n';
    buf[o + 1] = 0;
    out_s(e, buf);
    free(buf);
    return 0;
  }
  if (strcmp(name, "print") == 0) {
    size_t total = 0;
    for (size_t i = 0; i < n; i++)
      total += strlen(resolve(args[i]));
    char *buf = malloc(total + 1);
    size_t o = 0;
    for (size_t i = 0; i < n; i++) {
      const char *s = resolve(args[i]);
      size_t L = strlen(s);
      memcpy(buf + o, s, L);
      o += L;
    }
    buf[o] = 0;
    out_s(e, buf);
    free(buf);
    return 0;
  }
  if (strcmp(name, "quit") == 0) {
    e->quit = true;
    return 0;
  }
  if (strcmp(name, "assert") == 0) {
    Fact f = fact_new(args, n);
    bool ok = engine_contains(e, &f);
    fact_free(&f);
    if (!ok) {
      err_s(e, "assert failed\n");
      return -1;
    }
    return 0;
  }
  if (strcmp(name, "assert-not") == 0) {
    Fact f = fact_new(args, n);
    bool ok = !engine_contains(e, &f);
    fact_free(&f);
    if (!ok) {
      err_s(e, "assert-not failed\n");
      return -1;
    }
    return 0;
  }
  if (strcmp(name, "-") == 0) {
    /* build pattern string and match/remove */
    if (n == 0)
      return 0;
    char *str = malloc(1);
    str[0] = 0;
    for (size_t i = 0; i < n; i++) {
      char *part = NULL;
      normal_form_fact(&(Fact){.args = (u32 *)&args[i], .len = 1}, &part);
      size_t o = strlen(str), L = strlen(part);
      str = realloc(str, o + L + 2);
      memcpy(str + o, part, L);
      str[o + L] = ' ';
      str[o + L + 1] = 0;
      free(part);
    }
    PatternFact pf;
    if (parse_pattern_fact(str, &pf) == 0) {
      for (size_t i = 0; i < e->facts.len;) {
        Bindings *m;
        size_t mn = pattern_fact_match(&pf, &e->facts.data[i], bing0(), &m);
        if (mn) {
          remove_fact(e, &e->facts.data[i]);
          for (size_t j = 0; j < mn; j++)
            bing_free(&m[j]);
          free(m);
        } else {
          i++;
        }
      }
      pf_free(&pf);
    } else {
      FactArr fs = {0};
      parse_facts(str, &fs);
      for (size_t i = 0; i < fs.len; i++)
        remove_fact(e, &fs.data[i]);
      FactArr_free(&fs);
    }
    free(str);
    return 0;
  }
  if (strcmp(name, "load") == 0) {
    if (n < 1)
      return 0;
    char path[4096];
    if (e->base_dir)
      snprintf(path, sizeof(path), "%s/%s", e->base_dir, resolve(args[0]));
    else
      snprintf(path, sizeof(path), "%s", resolve(args[0]));
    return engine_load_file(e, path);
  }
  if (strcmp(name, "panic") == 0) {
    size_t total = 0;
    for (size_t i = 0; i < n; i++)
      total += strlen(resolve(args[i])) + 1;
    char *buf = malloc(total + 8);
    size_t o = 0;
    for (size_t i = 0; i < n; i++) {
      const char *s = resolve(args[i]);
      size_t L = strlen(s);
      memcpy(buf + o, s, L);
      o += L;
      if (i < n - 1)
        buf[o++] = ' ';
    }
    buf[o] = 0;
    err_s(e, buf);
    free(buf);
    return -1;
  }
  if (strcmp(name, "facts") == 0) {
    for (size_t i = 0; i < e->facts.len; i++) {
      char *line;
      normal_form_fact(&e->facts.data[i], &line);
      size_t L = strlen(line);
      char *buf = malloc(L + 2);
      memcpy(buf, line, L);
      buf[L] = '\n';
      buf[L + 1] = 0;
      out_s(e, buf);
      free(buf);
      free(line);
    }
    return 0;
  }
  if (strcmp(name, "find") == 0) {
    char *str = malloc(1);
    str[0] = 0;
    for (size_t i = 0; i < n; i++) {
      size_t o = strlen(str), L = strlen(resolve(args[i]));
      str = realloc(str, o + L + 2);
      memcpy(str + o, resolve(args[i]), L);
      str[o + L] = ' ';
      str[o + L + 1] = 0;
    }
    Pattern pat;
    if (parse_pattern(str, &pat) == 0 && pat.n == 1 &&
        pat.items[0].kind == PI_FACT) {
      for (size_t i = 0; i < e->facts.len; i++) {
        Bindings *m;
        size_t mn = pattern_fact_match(&pat.items[0].fact, &e->facts.data[i],
                                       bing0(), &m);
        if (mn) {
          char *line;
          normal_form_fact(&e->facts.data[i], &line);
          size_t L = strlen(line);
          char *buf = malloc(L + 2);
          memcpy(buf, line, L);
          buf[L] = '\n';
          buf[L + 1] = 0;
          out_s(e, buf);
          free(buf);
          free(line);
        }
        for (size_t j = 0; j < mn; j++) {
          bing_free(&m[j]);
        }
        free(m);
      }
      pattern_free(&pat);
    } else {
      if (pat.n)
        pattern_free(&pat);
    }
    free(str);
    return 0;
  }
  return 0; /* unknown command: ignore */
}

static Bindings *bing0(void) {
  static Bindings b0 = {0};
  return &b0;
}

/* pattern_fact_match from matcher.c (non-static) */
extern size_t pattern_fact_match(const PatternFact *pf, const Fact *fact,
                                 const Bindings *bindings, Bindings **out);
extern void native_scalars(const Pattern *p, U32Arr *out);
extern void match_items_detailed(const PatternItem *items, size_t n,
                                 const Fact *facts, size_t nfacts,
                                 const bool *used, const Bindings *b,
                                 const U32Arr *native, ItemMatch **out,
                                 size_t *outn);
extern void im_free(ItemMatch *m);

/* turn loop */
int engine_run(Engine *e) {
  if (e->quit)
    return 0;
  /* fired tracking: per-rule set of matched-fact-sets. We store consumed index
   * sets. */
  /* For dedup, we'll keep a simple list of (rule, sorted consumed indices) that
   * fired. */
  size_t fired_n = 0;
  u32 *fired_rule = NULL;
  size_t **fired_facts = NULL;
  size_t *fired_fn = NULL;
  size_t iterations = 0;
  size_t i = 0;
  while (i < e->nrules) {
    iterations++;
    if (iterations > e->max_iterations) {
      err_s(e, "no fixpoint\n");
      return -1;
    }
    u32 name = e->names[i];
    Pattern pat = e->pats[i];
    Body body = e->bodies[i];
    /* snapshot facts (we mutate while iterating; collect matches first) */
    FactArr snap = e->facts;
    snap.data = malloc(e->facts.len * sizeof(Fact));
    snap.len = e->facts.len;
    snap.cap = snap.len;
    for (size_t k = 0; k < snap.len; k++) {
      snap.data[k].len = e->facts.data[k].len;
      snap.data[k].args = malloc(snap.data[k].len * sizeof(u32));
      memcpy(snap.data[k].args, e->facts.data[k].args,
             snap.data[k].len * sizeof(u32));
    }
    U32Arr native = {0};
    native_scalars(&pat, &native);
    bool *used0 = calloc(snap.len, sizeof(bool));
    ItemMatch *matches = NULL;
    size_t mn = 0;
    match_items_detailed(pat.items, pat.n, snap.data, snap.len, used0, bing0(),
                         &native, &matches, &mn);
    free(used0);
    U32Arr_free(&native);
    bool changed = false;
    for (size_t m = 0; m < mn; m++) {
      ItemMatch *match = &matches[m];
      /* build matched-fact set (sorted) for dedup */
      size_t nf = 0;
      size_t *ff = NULL;
      for (size_t g = 0; g < match->ngroups; g++) {
        for (size_t gi = 0; gi < match->glens[g]; gi++) {
          ff = realloc(ff, (nf + 1) * sizeof(size_t));
          ff[nf++] = match->groups[g][gi];
        }
      }
      /* sort */
      for (size_t a = 0; a < nf; a++)
        for (size_t b = a + 1; b < nf; b++)
          if (ff[b] < ff[a]) {
            size_t t = ff[a];
            ff[a] = ff[b];
            ff[b] = t;
          }
      bool seen = false;
      for (size_t f = 0; f < fired_n; f++)
        if (fired_rule[f] == name && fired_fn[f] == nf) {
          bool same = true;
          for (size_t q = 0; q < nf; q++)
            if (fired_facts[f][q] != ff[q]) {
              same = false;
              break;
            }
          if (same)
            seen = true;
        }
      if (seen) {
        free(ff);
        continue;
      }
      /* record fired */
      fired_rule = realloc(fired_rule, (fired_n + 1) * sizeof(u32));
      fired_facts = realloc(fired_facts, (fired_n + 1) * sizeof(size_t *));
      fired_fn = realloc(fired_fn, (fired_n + 1) * sizeof(size_t));
      fired_rule[fired_n] = name;
      fired_facts[fired_n] = ff;
      fired_fn[fired_n] = nf;
      fired_n++;
      /* removals from - items */
      for (size_t g = 0; g < match->ngroups; g++) {
        bool removed = false;
        if (g < pat.n) {
          if (pat.items[g].kind == PI_FACT)
            removed = pat.items[g].fact.removed;
          else {
            for (size_t f2 = 0; f2 < pat.items[g].rep.n && !removed; f2++)
              if (pat.items[g].rep.facts[f2].removed)
                removed = true;
          }
        }
        if (removed) {
          for (size_t gi = 0; gi < match->glens[g]; gi++) {
            if (match->groups[g][gi] < snap.len)
              remove_fact(e, &snap.data[match->groups[g][gi]]);
          }
        }
      }
      /* render body */
      char *text = malloc(1);
      text[0] = 0;
      render_chunks(body.chunks, body.n, &match->b, &text);
      if (e->trace) {
        char msg[1024];
        snprintf(msg, sizeof(msg), "[trace] fire %s -> %s\n", resolve(name),
                 text);
        err_s(e, msg);
      }
      if (text[0] && strcmp(text, "") != 0) {
        char *trimmed = text;
        while (*trimmed == ' ' || *trimmed == '\n' || *trimmed == '\t')
          trimmed++;
        if (*trimmed) {
          FactArr out = {0};
          parse_facts(text, &out);
          for (size_t fi = 0; fi < out.len; fi++) {
            /* transfer ownership to ingest_body; it frees the fact */
            Fact f = out.data[fi];
            out.data[fi].args = NULL;
            out.data[fi].len = 0;
            int rc = ingest_body(e, &f);
            if (rc) {
              free(text);
              for (size_t q = 0; q < out.len; q++)
                if (out.data[q].args)
                  fact_free(&out.data[q]);
              free(out.data);
              goto fail;
            }
          }
          FactArr_free(&out);
          changed = true;
        }
      }
      free(text);
    }
    /* free matches */
    for (size_t m = 0; m < mn; m++)
      im_free(&matches[m]);
    free(matches);
    /* free snapshot */
    for (size_t k = 0; k < snap.len; k++)
      fact_free(&snap.data[k]);
    free(snap.data);
    if (changed) {
      i = 0;
    } else
      i++;
  }
  /* free fired */
  for (size_t f = 0; f < fired_n; f++)
    free(fired_facts[f]);
  free(fired_rule);
  free(fired_facts);
  free(fired_fn);
  return 0;
fail:
  for (size_t f = 0; f < fired_n; f++)
    free(fired_facts[f]);
  free(fired_rule);
  free(fired_facts);
  free(fired_fn);
  return -1;
}

/* ingest a fact from a body or file. Returns 0 ok, -1 error. */
int ingest_body(Engine *e, Fact *fact) {
  if (fact->len == 0) {
    fact_free(fact);
    return 0;
  }
  /* strip leading "$" */
  Fact stored;
  const char *first = resolve(fact->args[0]);
  if (strcmp(first, "$") == 0) {
    stored = fact_new(fact->args + 1, fact->len - 1);
    fact_free(fact);
  } else
    stored = *fact;
  /* is_rule? */
  if (stored.len >= 4 && strcmp(resolve(stored.args[0]), "rule") == 0) {
    /* parse rule: rule name pattern body [spec] */
    const char *pat_s = resolve(stored.args[2]);
    const char *bod_s = resolve(stored.args[3]);
    Pattern pat;
    Body body;
    if (parse_pattern(pat_s, &pat) != 0) {
      fact_free(&stored);
      return -1;
    }
    parse_body(bod_s, &body);
    i64 base = pattern_spec(&pat);
    if (stored.len == 5) {
      const char *s = resolve(stored.args[4]);
      int sign = 0;
      const char *dig = s;
      if (s[0] == '+') {
        sign = 1;
        dig = s + 1;
      } else if (s[0] == '-') {
        sign = -1;
        dig = s + 1;
      } else if (s[0] == '=') {
        sign = 2;
        dig = s + 1;
      }
      long n = atol(dig);
      if (sign == 1)
        base += n;
      else if (sign == -1)
        base -= n;
      else if (sign == 2)
        base = n;
    }
    add_rule(e, stored.args[1], base, pat, body);
    add_fact(e, &stored);
    return 0;
  }
  /* command? (first arg matches a known command name) */
  const char *cmd = resolve(stored.args[0]);
  if (strcmp(cmd, "println") == 0 || strcmp(cmd, "print") == 0 ||
      strcmp(cmd, "quit") == 0 || strcmp(cmd, "assert") == 0 ||
      strcmp(cmd, "assert-not") == 0 || strcmp(cmd, "-") == 0 ||
      strcmp(cmd, "load") == 0 || strcmp(cmd, "panic") == 0 ||
      strcmp(cmd, "facts") == 0 || strcmp(cmd, "find") == 0) {
    int rc = dispatch_command(e, cmd, stored.args + 1, stored.len - 1);
    fact_free(&stored);
    return rc;
  }
  /* regular fact */
  reduce_evals(e, &stored);
  add_fact(e, &stored);
  return 0;
}

/* load_str: parse facts, ingest each with file-level prefixing, settle after
 * each. */
int engine_load_str(Engine *e, const char *src) {
  FactArr out = {0};
  if (parse_facts(src, &out) != 0) {
    FactArr_free(&out);
    return -1;
  }
  for (size_t i = 0; i < out.len; i++) {
    /* prefix like the Rust ingest_file: $ -> strip, > -> prompt, else -> parse
     */
    const char *first = out.data[i].len ? resolve(out.data[i].args[0]) : "";
    Fact f;
    if (out.data[i].len && strcmp(first, "$") == 0) {
      f = fact_new(out.data[i].args + 1, out.data[i].len - 1);
      fact_free(&out.data[i]);
    } else if (out.data[i].len && strcmp(first, ">") == 0) {
      u32 *a = malloc(out.data[i].len * sizeof(u32));
      a[0] = intern("prompt", 6);
      for (size_t k = 1; k < out.data[i].len; k++)
        a[k] = out.data[i].args[k];
      f = fact_new(a, out.data[i].len);
      free(a);
      fact_free(&out.data[i]);
    } else {
      u32 *a = malloc((out.data[i].len + 1) * sizeof(u32));
      a[0] = intern("parse", 5);
      for (size_t k = 0; k < out.data[i].len; k++)
        a[k + 1] = out.data[i].args[k];
      f = fact_new(a, out.data[i].len + 1);
      free(a);
      fact_free(&out.data[i]);
    }
    int rc = ingest_body(e, &f);
    if (rc) {
      FactArr_free(&out);
      return rc;
    }
    if (e->quit)
      break;
    int r2 = engine_run(e);
    if (r2) {
      FactArr_free(&out);
      return r2;
    }
  }
  FactArr_free(&out);
  return 0;
}

int engine_load_file(Engine *e, const char *path) {
  FILE *fp = fopen(path, "r");
  if (!fp) {
    err_s(e, "load: cannot open ");
    err_s(e, path);
    err_s(e, "\n");
    return -1;
  }
  size_t cap = 4096, len = 0;
  char *buf = malloc(cap);
  size_t r;
  while ((r = fread(buf + len, 1, cap - len, fp)) > 0) {
    len += r;
    if (len == cap) {
      cap *= 2;
      buf = realloc(buf, cap);
    }
  }
  fclose(fp);
  buf[len] = 0;
  /* resolve `$ load` relative paths against this file's parent dir */
  char *saved = e->base_dir;
  char dir[4096];
  strncpy(dir, path, sizeof(dir) - 1);
  dir[sizeof(dir) - 1] = 0;
  char *slash = strrchr(dir, '/');
  if (slash) {
    *slash = 0;
    e->base_dir = strdup(dir);
  } else
    e->base_dir = strdup(".");
  int rc = engine_load_str(e, buf);
  free(buf);
  free(e->base_dir);
  e->base_dir = saved;
  return rc;
}
