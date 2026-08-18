/* core.c — interner, arena, dynamic arrays, facts, bindings, normal form. */
#include "reform.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- interner ---------- */
/* Entries store an OFFSET into g_arena, not a pointer: g_arena is realloc'd
 * on growth, which would invalidate stored pointers. Resolve on demand. */
typedef struct {
  size_t off;
  size_t len;
  u32 id;
} InternEntry;

static InternEntry *g_entries = NULL;
static size_t g_n = 0, g_cap = 0;
static char *g_arena = NULL; /* string storage */
static size_t g_alen = 0, g_acap = 0;

static u32 find_intern(const char *s, size_t len) {
  for (size_t i = 0; i < g_n; i++)
    if (g_entries[i].len == len &&
        memcmp(g_arena + g_entries[i].off, s, len) == 0)
      return g_entries[i].id;
  return (u32)-1;
}
u32 intern(const char *s, size_t len) {
  u32 f = find_intern(s, len);
  if (f != (u32)-1)
    return f;
  if (g_alen + len + 1 > g_acap) {
    g_acap = g_acap ? g_acap * 2 : 1024;
    while (g_alen + len + 1 > g_acap)
      g_acap *= 2;
    g_arena = realloc(g_arena, g_acap);
  }
  char *c = g_arena + g_alen;
  memcpy(c, s, len);
  c[len] = 0;
  if (g_n == g_cap) {
    g_cap = g_cap ? g_cap * 2 : 256;
    g_entries = realloc(g_entries, g_cap * sizeof(InternEntry));
  }
  g_entries[g_n].off = g_alen;
  g_entries[g_n].len = len;
  g_entries[g_n].id = (u32)g_n;
  g_alen += len + 1;
  return (u32)g_n++;
}
const char *resolve(u32 id) { return g_arena + g_entries[id].off; }

/* ---------- arrays ---------- */
void U32Arr_push(U32Arr *a, u32 v) {
  if (a->len == a->cap) {
    a->cap = a->cap ? a->cap * 2 : 8;
    a->data = realloc(a->data, a->cap * sizeof(u32));
  }
  a->data[a->len++] = v;
}
void U32Arr_free(U32Arr *a) {
  free(a->data);
  a->data = NULL;
  a->len = a->cap = 0;
}

void FactArr_push(FactArr *a, Fact v) {
  if (a->len == a->cap) {
    a->cap = a->cap ? a->cap * 2 : 8;
    a->data = realloc(a->data, a->cap * sizeof(Fact));
  }
  a->data[a->len++] = v;
}
void FactArr_free(FactArr *a) {
  for (size_t i = 0; i < a->len; i++)
    fact_free(&a->data[i]);
  free(a->data);
  a->data = NULL;
  a->len = a->cap = 0;
}

/* ---------- facts ---------- */
Fact fact_new(const u32 *args, size_t len) {
  Fact f;
  f.len = len;
  f.args = malloc(len * sizeof(u32));
  if (len)
    memcpy(f.args, args, len * sizeof(u32));
  return f;
}
bool fact_eq(const Fact *a, const Fact *b) {
  if (a->len != b->len)
    return false;
  return memcmp(a->args, b->args, a->len * sizeof(u32)) == 0;
}
void fact_free(Fact *f) {
  free(f->args);
  f->args = NULL;
  f->len = 0;
}
bool fact_is_rule(const Fact *f) {
  if (f->len < 4)
    return false;
  const char *s = resolve(f->args[0]);
  return strlen(s) == 4 && memcmp(s, "rule", 4) == 0;
}

/* ---------- normal form ---------- */
const char *normal_form_arg(u32 arg) {
  const char *s = resolve(arg);
  size_t n = strlen(s);
  if (n == 0) {
    static const char *e = "()";
    return e;
  }
  bool needs = false;
  for (size_t i = 0; i < n; i++) {
    char c = s[i];
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '(' ||
        c == ')' || c == '`') {
      needs = true;
      break;
    }
  }
  if (!needs && n &&
      (s[n - 1] == ';' || s[n - 1] == '.' || s[n - 1] == ':' ||
       s[n - 1] == '\''))
    needs = true;
  if (!needs)
    return s;
  /* build "(...)" with escaping */
  static char buf[4096];
  size_t o = 0;
  buf[o++] = '(';
  for (size_t i = 0; i < n && o < 4090; i++) {
    char c = s[i];
    if (c == '\\') {
      buf[o++] = '\\';
      buf[o++] = '\\';
    } else if (c == '(') {
      buf[o++] = '\\';
      buf[o++] = '(';
    } else if (c == ')') {
      buf[o++] = '\\';
      buf[o++] = ')';
    } else
      buf[o++] = c;
  }
  buf[o++] = ')';
  buf[o] = 0;
  static char *ret;
  ret = buf;
  return ret;
}
void normal_form_fact(const Fact *f, char **out) {
  /* compute total length first, then write */
  size_t total = 0;
  for (size_t i = 0; i < f->len; i++)
    total += strlen(normal_form_arg(f->args[i]));
  *out = malloc(total + f->len);
  char *p = *out;
  *p = 0;
  for (size_t i = 0; i < f->len; i++) {
    if (i)
      *p++ = ' ';
    const char *part = normal_form_arg(f->args[i]);
    size_t L = strlen(part);
    memcpy(p, part, L);
    p += L;
  }
  *p = 0;
}

/* ---------- bindings ---------- */
void bv_free(BindValue *v) {
  if (v->kind == BV_MANY) {
    for (size_t i = 0; i < v->many.len; i++)
      bv_free(&v->many.items[i]);
    free(v->many.items);
  }
}
void bing_init(Bindings *b) {
  b->names = NULL;
  b->vals = NULL;
  b->len = b->cap = 0;
}
void bing_free(Bindings *b) {
  for (size_t i = 0; i < b->len; i++)
    bv_free(&b->vals[i]);
  free(b->names);
  free(b->vals);
  bing_init(b);
}
BindValue *bing_get(Bindings *b, u32 name) {
  for (size_t i = 0; i < b->len; i++)
    if (b->names[i] == name)
      return &b->vals[i];
  return NULL;
}
static void bing_set(Bindings *b, u32 name, BindValue v) {
  for (size_t i = 0; i < b->len; i++)
    if (b->names[i] == name) {
      bv_free(&b->vals[i]);
      b->vals[i] = v;
      return;
    }
  if (b->len == b->cap) {
    b->cap = b->cap ? b->cap * 2 : 8;
    b->names = realloc(b->names, b->cap * sizeof(u32));
    b->vals = realloc(b->vals, b->cap * sizeof(BindValue));
  }
  b->names[b->len] = name;
  b->vals[b->len] = v;
  b->len++;
}
bool bing_bind_scalar(Bindings *b, u32 name, u32 val) {
  BindValue *ex = bing_get(b, name);
  if (!ex) {
    BindValue v;
    v.kind = BV_ONE;
    v.one = val;
    v.many.items = NULL;
    v.many.len = v.many.cap = 0;
    bing_set(b, name, v);
    return true;
  }
  if (ex->kind == BV_ONE)
    return ex->one == val;
  /* Many: append */
  bv_push(ex, (BindValue){.kind = BV_ONE, .one = val});
  return true;
}
static void bv_copy_into(BindValue *dst, const BindValue *src);
void bv_push(BindValue *many, BindValue child) {
  if (many->many.len == many->many.cap) {
    many->many.cap = many->many.cap ? many->many.cap * 2 : 4;
    many->many.items =
        realloc(many->many.items, many->many.cap * sizeof(BindValue));
  }
  many->many.items[many->many.len] = child;
  /* deep-copy the child so nested Many lists aren't shared */
  many->many.items[many->many.len].many.items = NULL;
  many->many.items[many->many.len].many.len =
      many->many.items[many->many.len].many.cap = 0;
  if (child.kind == BV_MANY) {
    for (size_t i = 0; i < child.many.len; i++)
      bv_copy_into(&many->many.items[many->many.len], &child.many.items[i]);
  }
  many->many.len++;
}
static void bv_copy_into(BindValue *dst, const BindValue *src) {
  /* append src as a deep copy into dst's many list */
  if (dst->many.len == dst->many.cap) {
    dst->many.cap = dst->many.cap ? dst->many.cap * 2 : 4;
    dst->many.items =
        realloc(dst->many.items, dst->many.cap * sizeof(BindValue));
  }
  BindValue *slot = &dst->many.items[dst->many.len++];
  slot->kind = src->kind;
  if (src->kind == BV_ONE) {
    slot->one = src->one;
    slot->many.items = NULL;
    slot->many.len = slot->many.cap = 0;
  } else {
    slot->many.items = NULL;
    slot->many.len = slot->many.cap = 0;
    for (size_t i = 0; i < src->many.len; i++)
      bv_push(slot, src->many.items[i]);
  }
}
bool bv_eq(const BindValue *a, const BindValue *b) {
  if (a->kind != b->kind)
    return false;
  if (a->kind == BV_ONE)
    return a->one == b->one;
  if (a->many.len != b->many.len)
    return false;
  for (size_t i = 0; i < a->many.len; i++)
    if (!bv_eq(&a->many.items[i], &b->many.items[i]))
      return false;
  return true;
}
bool bing_merge(Bindings *dst, const Bindings *src) {
  for (size_t i = 0; i < src->len; i++) {
    u32 k = src->names[i];
    const BindValue *v = &src->vals[i];
    if (v->kind == BV_ONE) {
      if (!bing_bind_scalar(dst, k, v->one))
        return false;
    } else {
      BindValue *ex = bing_get(dst, k);
      if (ex && ex->kind == BV_MANY && bv_eq(ex, v)) {
      } else if (!ex) {
        BindValue nv;
        nv.kind = BV_MANY;
        nv.many.items = NULL;
        nv.many.len = nv.many.cap = 0;
        for (size_t j = 0; j < v->many.len; j++) {
          BindValue c = v->many.items[j];
          bv_push(&nv, c);
        }
        bing_set(dst, k, nv);
      } else
        return false;
    }
  }
  return true;
}

/* ---------- AST free functions ---------- */
void at_free(ArgTemplate *a) {
  if (a->kind == AT_REPEAT) {
    for (size_t i = 0; i < a->rep.n; i++)
      at_free(&a->rep.args[i]);
    free(a->rep.args);
  }
}
void pf_free(PatternFact *pf) {
  for (size_t i = 0; i < pf->n; i++)
    at_free(&pf->args[i]);
  free(pf->args);
}
void pi_free(PatternItem *pi) {
  if (pi->kind == PI_FACT)
    pf_free(&pi->fact);
  else {
    for (size_t i = 0; i < pi->rep.n; i++)
      pf_free(&pi->rep.facts[i]);
    free(pi->rep.facts);
  }
}
void pattern_free(Pattern *p) {
  for (size_t i = 0; i < p->n; i++)
    pi_free(&p->items[i]);
  free(p->items);
}
void bc_free(BodyChunk *c) {
  if (c->kind == BC_TEXT)
    free(c->text);
  else if (c->kind == BC_REPEAT) {
    for (size_t i = 0; i < c->rep.n; i++)
      bc_free(&c->rep.chunks[i]);
    free(c->rep.chunks);
  }
}
void body_free(Body *b) {
  for (size_t i = 0; i < b->n; i++)
    bc_free(&b->chunks[i]);
  free(b->chunks);
}

/* bing_set_into: replace-or-insert a binding (takes ownership of v). */
void bing_set_into(Bindings *b, u32 name, BindValue v) {
  for (size_t i = 0; i < b->len; i++)
    if (b->names[i] == name) {
      bv_free(&b->vals[i]);
      b->vals[i] = v;
      return;
    }
  if (b->len == b->cap) {
    b->cap = b->cap ? b->cap * 2 : 8;
    b->names = realloc(b->names, b->cap * sizeof(u32));
    b->vals = realloc(b->vals, b->cap * sizeof(BindValue));
  }
  b->names[b->len] = name;
  b->vals[b->len] = v;
  b->len++;
}

void im_free(ItemMatch *m) {
  bing_free(&m->b);
  for (size_t i = 0; i < m->ngroups; i++)
    free(m->groups[i]);
  free(m->groups);
  free(m->glens);
}
