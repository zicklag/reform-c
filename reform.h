/* reform.h — Reform rule engine in plain C (reduced spec).
 *
 * A from-scratch, un-optimized, correct implementation of the Reform
 * runtime, tested against the reference implementation's test suite.
 */
#ifndef REFORM_H
#define REFORM_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef uint32_t u32;
typedef int64_t i64;
typedef uint64_t u64;

/* ---- interner ---- */
u32 intern(const char *s, size_t len);
const char *resolve(u32 id);

/* ---- dynamic arrays ---- */
#define DA_DECL(NAME, T) \
    typedef struct { T *data; size_t len, cap; } NAME; \
    void NAME##_push(NAME *a, T v); \
    void NAME##_free(NAME *a)

DA_DECL(U32Arr, u32);

/* ---- facts ---- */
typedef struct { u32 *args; size_t len; } Fact;
DA_DECL(FactArr, Fact);

Fact fact_new(const u32 *args, size_t len);
bool fact_eq(const Fact *a, const Fact *b);
void fact_free(Fact *f);
bool fact_is_rule(const Fact *f);
const char *normal_form_arg(u32 arg);
void normal_form_fact(const Fact *f, char **out);

/* ---- placeholder values and bindings ---- */
typedef struct BindValue BindValue;
typedef enum { BV_ONE, BV_MANY } BVKind;
struct BindValue {
    BVKind kind;
    u32 one;
    struct { BindValue *items; size_t len, cap; } many;
};
void bv_free(BindValue *v);

typedef struct { u32 *names; BindValue *vals; size_t len, cap; } Bindings;
void bv_push(BindValue *many, BindValue child);
void bv_free(BindValue *v);
bool bv_eq(const BindValue *a, const BindValue *b);
void bing_set_into(Bindings *b, u32 name, BindValue v);
void bing_init(Bindings *b);
void bing_free(Bindings *b);
BindValue *bing_get(Bindings *b, u32 name);
bool bing_bind_scalar(Bindings *b, u32 name, u32 val);
bool bing_merge(Bindings *dst, const Bindings *src);

/* ---- pattern / body AST ---- */
typedef enum { RK_OPTIONAL, RK_ONEORMORE, RK_ZEROORMORE } RepKind;

typedef enum { AT_LIT, AT_PH, AT_REPEAT } ArgKind;
typedef struct ArgTemplate ArgTemplate;
typedef struct { RepKind kind; bool greedy; ArgTemplate *args; size_t n; } ArgRep;
struct ArgTemplate {
    ArgKind kind;
    u32 lit;
    u32 ph;
    ArgRep rep;
};
void at_free(ArgTemplate *a);

typedef struct { bool removed, negated; ArgTemplate *args; size_t n; } PatternFact;
void pf_free(PatternFact *pf);

typedef struct { RepKind kind; bool greedy; PatternFact *facts; size_t n; } FactRep;

typedef enum { PI_FACT, PI_FACTREP } PiKind;
typedef struct { PiKind kind; PatternFact fact; FactRep rep; } PatternItem;
void pi_free(PatternItem *pi);

typedef struct { PatternItem *items; size_t n; } Pattern;
void pattern_free(Pattern *p);

typedef enum { BC_TEXT, BC_PH, BC_REPEAT } BcKind;
typedef struct BodyChunk BodyChunk;
struct BodyChunk {
    BcKind kind;
    char *text;
    u32 ph;
    struct { RepKind kind; bool greedy; BodyChunk *chunks; size_t n; } rep;
};
void bc_free(BodyChunk *c);

typedef struct { BodyChunk *chunks; size_t n; } Body;
void body_free(Body *b);

/* ---- parsing ---- */
int parse_facts(const char *src, FactArr *out);
int parse_pattern(const char *src, Pattern *out);
void parse_body(const char *src, Body *out);
int parse_pattern_fact(const char *src, PatternFact *out);

typedef struct { Bindings b; size_t **groups; size_t *glens; size_t ngroups; } ItemMatch;
void im_free(ItemMatch *m);
size_t pattern_fact_match(const PatternFact *pf, const Fact *fact, const Bindings *bindings, Bindings **out);
void native_scalars(const Pattern *p, U32Arr *out);
void match_items_detailed(const PatternItem *items, size_t n, const Fact *facts, size_t nfacts,
                          const bool *used, const Bindings *b, const U32Arr *native,
                          ItemMatch **out, size_t *outn);

/* ---- engine ---- */
typedef struct Engine Engine;
Engine *engine_new(void);
void engine_free(Engine *);
void engine_set_base_dir(Engine *e, const char *path);
int engine_load_str(Engine *e, const char *src);
int engine_load_file(Engine *e, const char *path);
int engine_run(Engine *e);
bool engine_contains(Engine *e, const Fact *f);
int engine_set_seed(Engine *e, u64 seed);

typedef void (*Sink)(const char *s);
void engine_set_stdout(Engine *e, Sink s);
void engine_set_stderr(Engine *e, Sink s);

#endif
