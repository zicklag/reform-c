/* matcher.c — pattern matching: frame-stack accumulator, lazy backtracking,
 * ?-constraints, Many nesting. Mirrors src/rule.rs. */
#include "reform.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* In-progress matching state: completed bindings plus a stack of repetition
 * frames. Frames are (name, values) lists, mirroring the Rust State. */
typedef struct {
  u32 name;
  BindValue *vals;
  size_t len, cap;
} FrameSlot;
typedef struct {
  FrameSlot *slots;
  size_t n, cap;
} Frame;

typedef struct {
  Bindings b;
  Frame *frames;
  size_t nframes, capframes;
} State;

static void state_init(State *s) {
  bing_init(&s->b);
  s->frames = NULL;
  s->nframes = s->capframes = 0;
}
static void frame_slot_free(FrameSlot *fs) {
  for (size_t i = 0; i < fs->len; i++)
    bv_free(&fs->vals[i]);
  free(fs->vals);
}
static void state_free(State *s) {
  bing_free(&s->b);
  for (size_t i = 0; i < s->nframes; i++) {
    for (size_t j = 0; j < s->frames[i].n; j++)
      frame_slot_free(&s->frames[i].slots[j]);
    free(s->frames[i].slots);
  }
  free(s->frames);
}
static State state_clone(const State *s) {
  State o;
  bing_init(&o.b);
  o.b = s->b; /* shallow; fix below */
  o.b.names = NULL;
  o.b.vals = NULL;
  o.b.len = o.b.cap = 0;
  for (size_t i = 0; i < s->b.len; i++) {
    /* deep copy val */
    if (s->b.vals[i].kind == BV_ONE)
      bing_bind_scalar(&o.b, s->b.names[i], s->b.vals[i].one);
    else {
      BindValue nv;
      nv.kind = BV_MANY;
      nv.many.items = NULL;
      nv.many.len = nv.many.cap = 0;
      for (size_t j = 0; j < s->b.vals[i].many.len; j++)
        bv_push(&nv, s->b.vals[i].many.items[j]);
      /* set without overwriting (bing_set replaces; but name may exist) */
      for (size_t k = 0; k < o.b.len; k++)
        if (o.b.names[k] == s->b.names[i]) {
          o.b.vals[k] = nv;
          goto next;
        }
      if (o.b.len == o.b.cap) {
        o.b.cap = o.b.cap ? o.b.cap * 2 : 8;
        o.b.names = realloc(o.b.names, o.b.cap * sizeof(u32));
        o.b.vals = realloc(o.b.vals, o.b.cap * sizeof(BindValue));
      }
      o.b.names[o.b.len] = s->b.names[i];
      o.b.vals[o.b.len] = nv;
      o.b.len++;
    next:;
    }
  }
  o.frames = NULL;
  o.nframes = o.capframes = 0;
  for (size_t i = 0; i < s->nframes; i++) {
    Frame f;
    f.slots = NULL;
    f.n = 0;
    f.cap = 0;
    for (size_t j = 0; j < s->frames[i].n; j++) {
      if (f.n == f.cap) {
        f.cap = f.cap ? f.cap * 2 : 4;
        f.slots = realloc(f.slots, f.cap * sizeof(FrameSlot));
      }
      FrameSlot fs;
      fs.name = s->frames[i].slots[j].name;
      fs.vals = NULL;
      fs.len = fs.cap = 0;
      for (size_t k = 0; k < s->frames[i].slots[j].len; k++) {
        /* deep copy s->frames[i].slots[j].vals[k] into fs.vals */
        if (fs.len == fs.cap) {
          fs.cap = fs.cap ? fs.cap * 2 : 4;
          fs.vals = realloc(fs.vals, fs.cap * sizeof(BindValue));
        }
        fs.vals[fs.len] = s->frames[i].slots[j].vals[k];
        fs.vals[fs.len].many.items = NULL;
        fs.vals[fs.len].many.len = fs.vals[fs.len].many.cap = 0;
        if (s->frames[i].slots[j].vals[k].kind == BV_MANY) {
          for (size_t m = 0; m < s->frames[i].slots[j].vals[k].many.len; m++)
            bv_push(&fs.vals[fs.len],
                    s->frames[i].slots[j].vals[k].many.items[m]);
        }
        fs.len++;
      }
      f.slots[f.n++] = fs;
    }
    if (o.nframes == o.capframes) {
      o.capframes = o.capframes ? o.capframes * 2 : 4;
      o.frames = realloc(o.frames, o.capframes * sizeof(Frame));
    }
    o.frames[o.nframes++] = f;
  }
  return o;
}

/* append val to innermost frame slot for name */
static void state_append(State *s, u32 name, BindValue val) {
  Frame *frame = &s->frames[s->nframes - 1];
  FrameSlot *slot = NULL;
  for (size_t i = 0; i < frame->n; i++)
    if (frame->slots[i].name == name) {
      slot = &frame->slots[i];
      break;
    }
  if (!slot) { /* shouldn't happen: pre-seeded */
    return;
  }
  if (slot->len == slot->cap) {
    slot->cap = slot->cap ? slot->cap * 2 : 4;
    slot->vals = realloc(slot->vals, slot->cap * sizeof(BindValue));
  }
  slot->vals[slot->len++] = val;
}
/* push a frame pre-seeded with all placeholders in the repetition's args */
static void collect_ph_args(const ArgTemplate *args, size_t n, U32Arr *out);
static void state_push_frame(State *s, const ArgTemplate *args, size_t n) {
  U32Arr phs = {0};
  collect_ph_args(args, n, &phs);
  Frame f;
  f.slots = NULL;
  f.n = 0;
  f.cap = 0;
  for (size_t i = 0; i < phs.len; i++) {
    if (f.n == f.cap) {
      f.cap = f.cap ? f.cap * 2 : 4;
      f.slots = realloc(f.slots, f.cap * sizeof(FrameSlot));
    }
    FrameSlot fs;
    fs.name = phs.data[i];
    fs.vals = NULL;
    fs.len = fs.cap = 0;
    f.slots[f.n++] = fs;
  }
  U32Arr_free(&phs);
  if (s->nframes == s->capframes) {
    s->capframes = s->capframes ? s->capframes * 2 : 4;
    s->frames = realloc(s->frames, s->capframes * sizeof(Frame));
  }
  s->frames[s->nframes++] = f;
}
static void collect_ph_args(const ArgTemplate *args, size_t n, U32Arr *out) {
  for (size_t i = 0; i < n; i++) {
    if (args[i].kind == AT_PH)
      U32Arr_push(out, args[i].ph);
    else if (args[i].kind == AT_REPEAT)
      collect_ph_args(args[i].rep.args, args[i].rep.n, out);
  }
}
/* pop innermost frame, fold lists into parent or root */
static void state_promote(State *s) {
  Frame frame = s->frames[s->nframes - 1];
  s->nframes--;
  for (size_t i = 0; i < frame.n; i++) {
    u32 name = frame.slots[i].name;
    BindValue group;
    group.kind = BV_MANY;
    group.many.items = NULL;
    group.many.len = group.many.cap = 0;
    for (size_t j = 0; j < frame.slots[i].len; j++)
      bv_push(&group, frame.slots[i].vals[j]);
    if (s->nframes > 0) {
      Frame *outer = &s->frames[s->nframes - 1];
      FrameSlot *slot = NULL;
      for (size_t k = 0; k < outer->n; k++)
        if (outer->slots[k].name == name) {
          slot = &outer->slots[k];
          break;
        }
      if (slot) {
        if (slot->len == slot->cap) {
          slot->cap = slot->cap ? slot->cap * 2 : 4;
          slot->vals = realloc(slot->vals, slot->cap * sizeof(BindValue));
        }
        slot->vals[slot->len++] = group;
      } else { /* shouldn't happen */
      }
    } else {
      bing_set_into(&s->b, name, group);
    }
  }
  for (size_t i = 0; i < frame.n; i++)
    frame_slot_free(&frame.slots[i]);
  free(frame.slots);
}

typedef struct {
  size_t end;
  State st;
} ArgMatch;
void bing_set_into(Bindings *b, u32 name, BindValue v);
static ArgMatch *match_args(const ArgTemplate *args, size_t n,
                            const u32 *fact_args, size_t fn, size_t start,
                            const State *st, size_t *outn);
static ArgMatch *match_reps_impl(const ArgTemplate *inner, size_t in,
                                 const u32 *fact_args, size_t fn, size_t start,
                                 const State *st, bool at_least_one,
                                 bool greedy, const ArgTemplate *rest,
                                 size_t rn, size_t *outn);

/* append results of `inner` (a match_args call) into a buffer */
static void extend_matches(ArgMatch **out, size_t *outn, size_t *outcap,
                           const ArgMatch *src, size_t sn) {
  for (size_t i = 0; i < sn; i++) {
    if (*outn == *outcap) {
      *outcap = *outcap ? *outcap * 2 : 16;
      *out = realloc(*out, *outcap * sizeof(ArgMatch));
    }
    (*out)[(*outn)++] = src[i];
  }
}

/* match a sequence of arg templates against fact args from `start`, returning
 * all (end, state). */
static ArgMatch *match_args(const ArgTemplate *args, size_t n,
                            const u32 *fact_args, size_t fn, size_t start,
                            const State *st, size_t *outn) {
  *outn = 0;
  if (n == 0) {
    ArgMatch *r = malloc(sizeof(ArgMatch));
    r[0].end = start;
    r[0].st = state_clone(st);
    *outn = 1;
    return r;
  }
  const ArgTemplate *first = &args[0];
  const ArgTemplate *rest = args + 1;
  size_t rn = n - 1;
  ArgMatch *acc = NULL;
  size_t accn = 0, acccap = 0;
  switch (first->kind) {
  case AT_LIT: {
    if (start < fn && fact_args[start] == first->lit) {
      size_t sn = 0;
      ArgMatch *sub = match_args(rest, rn, fact_args, fn, start + 1, st, &sn);
      extend_matches(&acc, &accn, &acccap, sub, sn);
      free(sub);
    }
    break;
  }
  case AT_PH: {
    if (start < fn) {
      State s = state_clone(st);
      if (s.nframes == 0) {
        if (bing_bind_scalar(&s.b, first->ph, fact_args[start])) {
          size_t sn = 0;
          ArgMatch *sub =
              match_args(rest, rn, fact_args, fn, start + 1, &s, &sn);
          extend_matches(&acc, &accn, &acccap, sub, sn);
          free(sub);
        }
      } else {
        state_append(&s, first->ph,
                     (BindValue){.kind = BV_ONE, .one = fact_args[start]});
        size_t sn = 0;
        ArgMatch *sub = match_args(rest, rn, fact_args, fn, start + 1, &s, &sn);
        extend_matches(&acc, &accn, &acccap, sub, sn);
        free(sub);
      }
      state_free(&s);
    }
    break;
  }
  case AT_REPEAT: {
    const ArgRep *r = &first->rep;
    State s = state_clone(st);
    state_push_frame(&s, r->args, r->n);
    size_t tmpn = 0;
    if (r->kind == RK_OPTIONAL) {
      ArgMatch *inner =
          match_args(r->args, r->n, fact_args, fn, start, &s, &tmpn);
      ArgMatch *one_res = NULL;
      size_t onen = 0, onecap = 0;
      for (size_t i = 0; i < tmpn; i++) {
        State s3 = state_clone(&inner[i].st);
        state_promote(&s3);
        size_t sn = 0;
        ArgMatch *sub =
            match_args(rest, rn, fact_args, fn, inner[i].end, &s3, &sn);
        extend_matches(&one_res, &onen, &onecap, sub, sn);
        free(sub);
        state_free(&s3);
      }
      free(inner);
      ArgMatch *zero_res = NULL;
      size_t zeron = 0, zerocap = 0;
      {
        State s0 = state_clone(&s);
        state_promote(&s0);
        size_t sn = 0;
        ArgMatch *sub = match_args(rest, rn, fact_args, fn, start, &s0, &sn);
        extend_matches(&zero_res, &zeron, &zerocap, sub, sn);
        free(sub);
        state_free(&s0);
      }
      if (r->greedy) {
        extend_matches(&acc, &accn, &acccap, one_res, onen);
        extend_matches(&acc, &accn, &acccap, zero_res, zeron);
      } else {
        extend_matches(&acc, &accn, &acccap, zero_res, zeron);
        extend_matches(&acc, &accn, &acccap, one_res, onen);
      }
      free(one_res);
      free(zero_res);
    } else {
      bool at_least_one = r->kind == RK_ONEORMORE;
      size_t rn2 = 0;
      ArgMatch *reps = match_reps_impl(r->args, r->n, fact_args, fn, start, &s,
                                       at_least_one, r->greedy, rest, rn, &rn2);
      extend_matches(&acc, &accn, &acccap, reps, rn2);
      free(reps);
    }
    state_free(&s);
    break;
  }
  }
  *outn = accn;
  return acc;
}

/* match_reps: helper recursive */
static ArgMatch *match_reps_impl(const ArgTemplate *inner, size_t in,
                                 const u32 *fact_args, size_t fn, size_t start,
                                 const State *st, bool at_least_one,
                                 bool greedy, const ArgTemplate *rest,
                                 size_t rn, size_t *outn) {
  *outn = 0;
  ArgMatch *acc = NULL;
  size_t accn = 0, acccap = 0;
  if (greedy) {
    size_t inmn = 0;
    ArgMatch *inm = match_args(inner, in, fact_args, fn, start, st, &inmn);
    for (size_t i = 0; i < inmn; i++) {
      size_t mid = inm[i].end;
      if (mid == start) {
        if (at_least_one) {
          State s3 = state_clone(&inm[i].st);
          state_promote(&s3);
          size_t sn = 0;
          ArgMatch *sub = match_args(rest, rn, fact_args, fn, mid, &s3, &sn);
          extend_matches(&acc, &accn, &acccap, sub, sn);
          free(sub);
          state_free(&s3);
        }
      } else {
        size_t sn = 0;
        ArgMatch *sub =
            match_reps_impl(inner, in, fact_args, fn, mid, &inm[i].st, false,
                            greedy, rest, rn, &sn);
        extend_matches(&acc, &accn, &acccap, sub, sn);
        free(sub);
      }
    }
    free(inm);
    if (!at_least_one) {
      State s0 = state_clone(st);
      state_promote(&s0);
      size_t sn = 0;
      ArgMatch *sub = match_args(rest, rn, fact_args, fn, start, &s0, &sn);
      extend_matches(&acc, &accn, &acccap, sub, sn);
      free(sub);
      state_free(&s0);
    }
  } else {
    if (!at_least_one) {
      State s0 = state_clone(st);
      state_promote(&s0);
      size_t sn = 0;
      ArgMatch *sub = match_args(rest, rn, fact_args, fn, start, &s0, &sn);
      extend_matches(&acc, &accn, &acccap, sub, sn);
      free(sub);
      state_free(&s0);
    }
    size_t inmn = 0;
    ArgMatch *inm = match_args(inner, in, fact_args, fn, start, st, &inmn);
    for (size_t i = 0; i < inmn; i++) {
      size_t mid = inm[i].end;
      if (mid == start) {
        if (at_least_one) {
          State s3 = state_clone(&inm[i].st);
          state_promote(&s3);
          size_t sn = 0;
          ArgMatch *sub = match_args(rest, rn, fact_args, fn, mid, &s3, &sn);
          extend_matches(&acc, &accn, &acccap, sub, sn);
          free(sub);
          state_free(&s3);
        }
      } else {
        size_t sn = 0;
        ArgMatch *sub =
            match_reps_impl(inner, in, fact_args, fn, mid, &inm[i].st, false,
                            greedy, rest, rn, &sn);
        extend_matches(&acc, &accn, &acccap, sub, sn);
        free(sub);
      }
    }
    free(inm);
  }
  *outn = accn;
  return acc;
}

/* ================= fact-level matching ================= */

/* pattern_fact_match: every full match of a pattern fact against one fact,
 * starting from bindings, lazy-first. Returns array of Bindings. */
typedef struct {
  Bindings b;
} BRes;
size_t pattern_fact_match(const PatternFact *pf, const Fact *fact,
                          const Bindings *bindings, Bindings **out) {
  /* collect list-bound placeholders of this fact (inside arg repetitions) */
  /* list_bound = top-level placeholders inside any AT_REPEAT arg */
  U32Arr lb = {0};
  for (size_t i = 0; i < pf->n; i++)
    if (pf->args[i].kind == AT_REPEAT)
      collect_ph_args(&pf->args[i], 1, &lb);
  /* build initial State */
  State st;
  state_init(&st);
  /* expected: bindings for list-bound placeholders; scalars go to st.b */
  U32Arr expected_names = {0};
  BindValue *expected_vals = NULL;
  size_t expected_n = 0;
  for (size_t i = 0; i < bindings->len; i++) {
    u32 k = bindings->names[i];
    bool is_lb = false;
    for (size_t j = 0; j < lb.len; j++)
      if (lb.data[j] == k) {
        is_lb = true;
        break;
      }
    if (is_lb) {
      U32Arr_push(&expected_names, k);
      expected_vals =
          realloc(expected_vals, (expected_n + 1) * sizeof(BindValue));
      /* copy val */
      const BindValue *v = &bindings->vals[i];
      if (v->kind == BV_ONE) {
        expected_vals[expected_n].kind = BV_ONE;
        expected_vals[expected_n].one = v->one;
      } else {
        expected_vals[expected_n].kind = BV_MANY;
        expected_vals[expected_n].many.items = NULL;
        expected_vals[expected_n].many.len =
            expected_vals[expected_n].many.cap = 0;
        for (size_t m = 0; m < v->many.len; m++)
          bv_push(&expected_vals[expected_n], v->many.items[m]);
      }
      expected_n++;
    } else {

      /* deep copy into st.b */
      const BindValue *v = &bindings->vals[i];
      if (v->kind == BV_ONE)
        bing_bind_scalar(&st.b, k, v->one);
      else {
        BindValue nv;
        nv.kind = BV_MANY;
        nv.many.items = NULL;
        nv.many.len = nv.many.cap = 0;
        for (size_t m = 0; m < v->many.len; m++)
          bv_push(&nv, v->many.items[m]);
        bing_set_into(&st.b, k, nv);
      }
    }
  }

  /* run match_args */
  size_t an = 0;
  ArgMatch *am =
      match_args(pf->args, pf->n, fact->args, fact->len, 0, &st, &an);
  /* collect full matches (end == fact->len) that satisfy expected */
  size_t outcap = 0, outn = 0;
  Bindings *res = NULL;
  for (size_t i = 0; i < an; i++) {
    if (am[i].end == fact->len) {
      bool ok = true;
      for (size_t e = 0; e < expected_n && ok; e++) {
        BindValue *got = bing_get(&am[i].st.b, expected_names.data[e]);
        if (!got || !bv_eq(got, &expected_vals[e]))
          ok = false;
      }
      if (ok) {
        if (outn == outcap) {
          outcap = outcap ? outcap * 2 : 8;
          res = realloc(res, outcap * sizeof(Bindings));
        }
        res[outn] = am[i].st.b;
        /* detach so we don't free it twice */
        am[i].st.b.names = NULL;
        am[i].st.b.vals = NULL;
        am[i].st.b.len = am[i].st.b.cap = 0;
        outn++;
      }
    }
  }
  /* free ArgMatches */
  for (size_t i = 0; i < an; i++)
    state_free(&am[i].st);
  free(am);
  /* free expected */
  for (size_t e = 0; e < expected_n; e++)
    bv_free(&expected_vals[e]);
  free(expected_vals);
  U32Arr_free(&expected_names);
  U32Arr_free(&lb);
  state_free(&st);
  *out = res;
  return outn;
}

/* native scalars: placeholders whose native context is top-level (stack empty)
 */
static void collect_native_impl(const ArgTemplate *args, size_t n,
                                U32Arr *stack, U32Arr *out);
static void collect_native_items(const PatternItem *items, size_t n,
                                 U32Arr *stack, U32Arr *out) {
  for (size_t i = 0; i < n; i++) {
    if (items[i].kind == PI_FACT)
      collect_native_impl(items[i].fact.args, items[i].fact.n, stack, out);
    else {
      U32Arr_push(stack, 0);
      for (size_t f = 0; f < items[i].rep.n; f++)
        collect_native_impl(items[i].rep.facts[f].args, items[i].rep.facts[f].n,
                            stack, out);
      stack->len--;
    }
  }
}
static void collect_native_impl(const ArgTemplate *args, size_t n,
                                U32Arr *stack, U32Arr *out) {
  for (size_t i = 0; i < n; i++) {
    if (args[i].kind == AT_PH && stack->len == 0)
      U32Arr_push(out, args[i].ph);
    else if (args[i].kind == AT_REPEAT) {
      U32Arr_push(stack, 0);
      collect_native_impl(args[i].rep.args, args[i].rep.n, stack, out);
      stack->len--;
    }
  }
}
void native_scalars(const Pattern *p, U32Arr *out) {
  U32Arr stack = {0};
  collect_native_items(p->items, p->n, &stack, out);
  U32Arr_free(&stack);
}
static bool in_u32arr(const U32Arr *a, u32 v) {
  for (size_t i = 0; i < a->len; i++)
    if (a->data[i] == v)
      return true;
  return false;
}

/* A full match result: bindings + per-item consumed groups. Defined in
 * reform.h. */

/* list-bound placeholders of a fact: top-level Ph inside AT_REPEAT args */
/* match_fact_repetition_detailed (mirrors Rust). */
static void match_fact_rep_detail(const FactRep *rep, const Fact *facts,
                                  size_t nfacts, const bool *used,
                                  const Bindings *b, const PatternItem *rest,
                                  size_t rn, const U32Arr *native,
                                  ItemMatch **out, size_t *outn);
void match_items_detailed(const PatternItem *items, size_t n, const Fact *facts,
                          size_t nfacts, const bool *used, const Bindings *b,
                          const U32Arr *native, ItemMatch **out, size_t *outn) {
  *outn = 0;
  if (n == 0) {
    ItemMatch *r = malloc(sizeof(ItemMatch));
    r->b = *b;
    r->b.names = NULL;
    r->b.vals = NULL;
    r->b.len = r->b.cap = 0;
    /* deep copy bindings */
    for (size_t i = 0; i < b->len; i++) {
      const BindValue *v = &b->vals[i];
      if (v->kind == BV_ONE)
        bing_bind_scalar(&r->b, b->names[i], v->one);
      else {
        BindValue nv;
        nv.kind = BV_MANY;
        nv.many.items = NULL;
        nv.many.len = nv.many.cap = 0;
        for (size_t m = 0; m < v->many.len; m++) {
          bv_push(&nv, v->many.items[m]);
        }
        bing_set_into(&r->b, b->names[i], nv);
      }
    }
    r->groups = NULL;
    r->glens = NULL;
    r->ngroups = 0;
    *out = r;
    *outn = 1;
    return;
  }
  const PatternItem *first = &items[0];
  const PatternItem *rest_items = items + 1;
  size_t rn = n - 1;
  ItemMatch *acc = NULL;
  size_t accn = 0, acccap = 0;
  (void)used;
  if (first->kind == PI_FACT) {
    const PatternFact *pf = &first->fact;
    if (pf->negated) {
      bool any = false;
      for (size_t i = 0; i < nfacts && !any; i++) {
        Bindings *m;
        size_t mn = pattern_fact_match(pf, &facts[i], b, &m);
        if (mn)
          any = true;
        for (size_t j = 0; j < mn; j++)
          bing_free(&m[j]);
        free(m);
      }
      if (!any) {
        ItemMatch *sub = NULL;
        size_t sn = 0;
        match_items_detailed(rest_items, rn, facts, nfacts, used, b, native,
                             &sub, &sn);
        for (size_t i = 0; i < sn; i++) {
          sub[i].glens =
              realloc(sub[i].glens, (sub[i].ngroups + 1) * sizeof(size_t));
          sub[i].groups =
              realloc(sub[i].groups, (sub[i].ngroups + 1) * sizeof(size_t *));
          memmove(&sub[i].groups[1], &sub[i].groups[0],
                  sub[i].ngroups * sizeof(size_t *));
          memmove(&sub[i].glens[1], &sub[i].glens[0],
                  sub[i].ngroups * sizeof(size_t));
          sub[i].groups[0] = NULL;
          sub[i].glens[0] = 0;
          sub[i].ngroups++;
          if (accn == acccap) {
            acccap = acccap ? acccap * 2 : 8;
            acc = realloc(acc, acccap * sizeof(ItemMatch));
          }
          acc[accn++] = sub[i];
        }
        free(sub);
      }
    } else {
      for (size_t i = 0; i < nfacts; i++) {
        if (used[i])
          continue;
        bool *used2 = malloc(nfacts * sizeof(bool));
        memcpy(used2, used, nfacts * sizeof(bool));
        used2[i] = true;
        Bindings *ms;
        size_t mn = pattern_fact_match(pf, &facts[i], b, &ms);
        for (size_t mi = 0; mi < mn; mi++) {
          ItemMatch *sub = NULL;
          size_t sn = 0;
          match_items_detailed(rest_items, rn, facts, nfacts, used2, &ms[mi],
                               native, &sub, &sn);
          if (sn) {
            for (size_t s = 0; s < sn; s++) {
              sub[s].glens =
                  realloc(sub[s].glens, (sub[s].ngroups + 1) * sizeof(size_t));
              sub[s].groups = realloc(sub[s].groups,
                                      (sub[s].ngroups + 1) * sizeof(size_t *));
              memmove(&sub[s].groups[1], &sub[s].groups[0],
                      sub[s].ngroups * sizeof(size_t *));
              memmove(&sub[s].glens[1], &sub[s].glens[0],
                      sub[s].ngroups * sizeof(size_t));
              sub[s].groups[0] = malloc(sizeof(size_t));
              sub[s].groups[0][0] = i;
              sub[s].glens[0] = 1;
              sub[s].ngroups++;
              if (accn == acccap) {
                acccap = acccap ? acccap * 2 : 8;
                acc = realloc(acc, acccap * sizeof(ItemMatch));
              }
              acc[accn++] = sub[s];
            }
            free(sub);
            break; /* lazy-first: only laziest that satisfies rest */
          }
          free(sub);
        }
        for (size_t j = 0; j < mn; j++)
          bing_free(&ms[j]);
        free(ms);
        free(used2);
      }
    }
  } else {
    match_fact_rep_detail(&first->rep, facts, nfacts, used, b, rest_items, rn,
                          native, &acc, &accn);
  }
  *out = acc;
  *outn = accn;
}

/* ?-constraint fact-level repetition (mirrors Rust
 * match_fact_repetition_detailed) */
static void match_fact_rep_detail(const FactRep *rep, const Fact *facts,
                                  size_t nfacts, const bool *used,
                                  const Bindings *b, const PatternItem *rest,
                                  size_t rn, const U32Arr *native,
                                  ItemMatch **out, size_t *outn) {
  *outn = 0;
  if (rep->n != 1)
    return; /* multi-fact inner not supported */
  const PatternFact *pf = &rep->facts[0];
  /* list_ph: top-level placeholders in the inner fact's args */
  U32Arr list_ph = {0};
  for (size_t i = 0; i < pf->n; i++)
    if (pf->args[i].kind == AT_PH)
      U32Arr_push(&list_ph, pf->args[i].ph);
  bool is_optional = rep->kind == RK_OPTIONAL;
  bool disabled = false, must_match = false;
  for (size_t i = 0; i < list_ph.len; i++) {
    BindValue *v = bing_get((Bindings *)b, list_ph.data[i]);
    if (v && v->kind == BV_MANY) {
      if (v->many.len == 0) {
        if (is_optional)
          disabled = true;
      } else {
        if (is_optional)
          must_match = true;
      }
    }
  }
  /* match_b: for must_match, bind scalar One(first) for list_ph */
  Bindings mb = *b;
  mb.names = NULL;
  mb.vals = NULL;
  mb.len = mb.cap = 0;
  for (size_t i = 0; i < b->len; i++) {
    const BindValue *v = &b->vals[i];
    bool is_lp = in_u32arr(&list_ph, b->names[i]);
    if (must_match && is_lp && v->kind == BV_MANY && v->many.len) {
      bing_bind_scalar(&mb, b->names[i], v->many.items[0].one);
    } else if (v->kind == BV_ONE)
      bing_bind_scalar(&mb, b->names[i], v->one);
    else {
      BindValue nv;
      nv.kind = BV_MANY;
      nv.many.items = NULL;
      nv.many.len = nv.many.cap = 0;
      for (size_t m = 0; m < v->many.len; m++) {
        bv_push(&nv, v->many.items[m]);
      }
      bing_set_into(&mb, b->names[i], nv);
    }
  }
  /* find matching facts (consistent with mb), laziest binding each, in order */
  Bindings *matched = NULL;
  size_t matchedn = 0;
  size_t matchedcap = 0;
  size_t *matched_idx = NULL;
  size_t midx_n = 0, midx_cap = 0;
  for (size_t i = 0; i < nfacts; i++) {
    if (used[i])
      continue;
    Bindings *ms;
    size_t mn = pattern_fact_match(pf, &facts[i], &mb, &ms);
    if (mn) {
      /* take laziest (first) */
      if (matchedn == matchedcap) {
        matchedcap = matchedcap ? matchedcap * 2 : 4;
        matched = realloc(matched, matchedcap * sizeof(Bindings));
      }
      matched[matchedn] = ms[0];
      ms[0].names = NULL;
      ms[0].vals = NULL;
      ms[0].len = ms[0].cap = 0;
      matchedn++;
      if (midx_n == midx_cap) {
        midx_cap = midx_cap ? midx_cap * 2 : 4;
        matched_idx = realloc(matched_idx, midx_cap * sizeof(size_t));
      }
      matched_idx[midx_n++] = i;
    }
    for (size_t j = 0; j < mn; j++)
      bing_free(&ms[j]);
    free(ms);
  }
  ItemMatch *acc = NULL;
  size_t accn = 0, acccap = 0;
  /* take: Optional with match -> [first]; OneOrMore/ZeroOrMore -> all */
  size_t *take = NULL;
  size_t taken = 0;
  if (rep->kind == RK_OPTIONAL && midx_n && !disabled) {
    take = malloc(sizeof(size_t));
    take[0] = matched_idx[0];
    taken = 1;
  } else if (rep->kind == RK_ONEORMORE || rep->kind == RK_ZEROORMORE) {
    take = malloc(midx_n * sizeof(size_t));
    memcpy(take, matched_idx, midx_n * sizeof(size_t));
    taken = midx_n;
  }
  bool want_present = taken > 0;
  bool free_optional = is_optional && !disabled && !must_match;
  bool can_absent =
      (rep->kind == RK_OPTIONAL || rep->kind == RK_ZEROORMORE) && !must_match;
  bool want_absent =
      can_absent && (!want_present || (free_optional && midx_n > 0));
  /* present_results */
  if (want_present) {
    bool *used2 = malloc(nfacts * sizeof(bool));
    memcpy(used2, used, nfacts * sizeof(bool));
    Bindings b3 = *b;
    b3.names = NULL;
    b3.vals = NULL;
    b3.len = b3.cap = 0;
    for (size_t i = 0; i < b->len; i++) {
      const BindValue *v = &b->vals[i];
      if (v->kind == BV_ONE)
        bing_bind_scalar(&b3, b->names[i], v->one);
      else {
        BindValue nv;
        nv.kind = BV_MANY;
        nv.many.items = NULL;
        nv.many.len = nv.many.cap = 0;
        for (size_t m = 0; m < v->many.len; m++) {
          bv_push(&nv, v->many.items[m]);
        }
        bing_set_into(&b3, b->names[i], nv);
      }
    }
    if (!must_match) {
      for (size_t ti = 0; ti < taken; ti++)
        used2[take[ti]] = true;
      for (size_t i = 0; i < list_ph.len; i++) {
        u32 name = list_ph.data[i];
        if (in_u32arr(native, name))
          continue;
        BindValue listv;
        listv.kind = BV_MANY;
        listv.many.items = NULL;
        listv.many.len = listv.many.cap = 0;
        for (size_t m = 0; m < matchedn; m++) {
          bool in_take = false;
          for (size_t ti = 0; ti < taken && !in_take; ti++)
            if (matched_idx[m] == take[ti])
              in_take = true;
          if (!in_take)
            continue;
          BindValue *got = bing_get(&matched[m], name);
          if (got && got->kind == BV_ONE)
            bv_push(&listv, (BindValue){.kind = BV_ONE, .one = got->one});
        }
        if (listv.many.len)
          bing_set_into(&b3, name, listv);
        else
          bv_free(&listv);
      }
    }
    ItemMatch *sub = NULL;
    size_t sn = 0;
    match_items_detailed(rest, rn, facts, nfacts, used2, &b3, native, &sub,
                         &sn);
    for (size_t s = 0; s < sn; s++) {
      sub[s].glens =
          realloc(sub[s].glens, (sub[s].ngroups + 1) * sizeof(size_t));
      sub[s].groups =
          realloc(sub[s].groups, (sub[s].ngroups + 1) * sizeof(size_t *));
      memmove(&sub[s].groups[1], &sub[s].groups[0],
              sub[s].ngroups * sizeof(size_t *));
      memmove(&sub[s].glens[1], &sub[s].glens[0],
              sub[s].ngroups * sizeof(size_t));
      if (must_match) {
        sub[s].groups[0] = NULL;
        sub[s].glens[0] = 0;
      } else {
        sub[s].groups[0] = malloc(taken * sizeof(size_t));
        memcpy(sub[s].groups[0], take, taken * sizeof(size_t));
        sub[s].glens[0] = taken;
      }
      sub[s].ngroups++;
      if (accn == acccap) {
        acccap = acccap ? acccap * 2 : 8;
        acc = realloc(acc, acccap * sizeof(ItemMatch));
      }
      acc[accn++] = sub[s];
    }
    free(sub);
    bing_free(&b3);
    free(used2);
  }
  /* Fact-level repetitions are always greedy: present first, with absent
   * as a fallback only when taking leaves the rest unsatisfiable. */
  bool had_present = accn > 0;
  if (!had_present && want_absent) {
    ItemMatch *sub = NULL;
    size_t sn = 0;
    match_items_detailed(rest, rn, facts, nfacts, used, b, native, &sub, &sn);
    for (size_t s = 0; s < sn; s++) {
      sub[s].glens =
          realloc(sub[s].glens, (sub[s].ngroups + 1) * sizeof(size_t));
      sub[s].groups =
          realloc(sub[s].groups, (sub[s].ngroups + 1) * sizeof(size_t *));
      memmove(&sub[s].groups[1], &sub[s].groups[0],
              sub[s].ngroups * sizeof(size_t *));
      memmove(&sub[s].glens[1], &sub[s].glens[0],
              sub[s].ngroups * sizeof(size_t));
      sub[s].groups[0] = NULL;
      sub[s].glens[0] = 0;
      sub[s].ngroups++;
      if (accn == acccap) {
        acccap = acccap ? acccap * 2 : 8;
        acc = realloc(acc, acccap * sizeof(ItemMatch));
      }
      acc[accn++] = sub[s];
    }
    free(sub);
  }
  free(take);
  free(matched_idx);
  for (size_t i = 0; i < matchedn; i++)
    bing_free(&matched[i]);
  free(matched);
  bing_free(&mb);
  U32Arr_free(&list_ph);
  *out = acc;
  *outn = accn;
}
