/*
 * wu_charset.c
 *
 * 有限域 F_p 上多项式系统的吴特征列（Wu's characteristic set）方法求解
 * 基于 FLINT 库（nmod_mpoly / nmod_mpoly_factor）
 *
 * 相对朴素实现的优化：
 *   1. 完整分解树（因式分解分裂）：
 *      任何时刻出现的多项式 f（输入、伪除余式、初式）都先做不可约分解，
 *      Zero(P ∪ {f1*f2}) = Zero(P ∪ {f1}) ∪ Zero(P ∪ {f2})，
 *      系统按因子分裂为子系统入队。重数被丢弃（无平方化），
 *      使各分支的多项式次数和项数保持很小。
 *   2. 初式分支：Zero(F) = Zero(CS/J) ∪ ⋃ Zero(F ∪ CS ∪ {I_i})，
 *      每个非常数初式产生一个子系统，保证不漏解。
 *   3. 子系统去重 + DFS 工作队列 + 处理上限，防止分支爆炸。
 *   4. 伪除快速路径：初式为常数时用标量逆元，避免整体乘法导致项数膨胀。
 *   5. 可选 -f：利用 x^p = x（只求 F_p 有理点时成立）直接把所有指数
 *      约化到 < p，超高次输入（如 x^100000）立即降为低次。
 *
 * 用法:
 *   ./wu_charset [k] [p] [-f]
 *     k : 第一个方程为 x^k + y^k + z^k - 5（默认 1）
 *     p : 素数模（默认 13）
 *     -f: 开启 x^p = x 指数约化
 *
 * 编译（FLINT >= 3.0）:
 *   gcc -O2 -o wu_charset wu_charset.c -lflint -lgmp
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <flint/flint.h>
#include <flint/nmod.h>
#include <flint/nmod_mpoly.h>
#include <flint/nmod_mpoly_factor.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_poly_factor.h>

#define MAX_SPLIT_FACTORS 8     /* 因子多于此数时不分裂，只取无平方部分 */
#define MAX_SYSTEMS 20000       /* 处理的子系统总数上限 */
#define FREE_VAR_ENUM_LIMIT 4096
#define PRINT_COMPONENT_LIMIT 20

/* ------------------------------------------------------------------ */
/* 多项式集合                                                          */
/* ------------------------------------------------------------------ */

typedef struct
{
    nmod_mpoly_struct *p;
    slong len;
    slong alloc;
} polyset_t;

static void polyset_init(polyset_t *S)
{
    S->p = NULL;
    S->len = 0;
    S->alloc = 0;
}

static void polyset_clear(polyset_t *S, const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < S->len; i++)
        nmod_mpoly_clear(S->p + i, ctx);
    free(S->p);
    S->p = NULL;
    S->len = S->alloc = 0;
}

static void polyset_append(polyset_t *S, const nmod_mpoly_t f,
                           const nmod_mpoly_ctx_t ctx)
{
    if (S->len == S->alloc)
    {
        S->alloc = (S->alloc == 0) ? 8 : 2 * S->alloc;
        S->p = (nmod_mpoly_struct *)
                   realloc(S->p, S->alloc * sizeof(nmod_mpoly_struct));
    }
    nmod_mpoly_init(S->p + S->len, ctx);
    nmod_mpoly_set(S->p + S->len, f, ctx);
    S->len++;
}

static int polyset_contains(const polyset_t *S, const nmod_mpoly_t f,
                            const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < S->len; i++)
        if (nmod_mpoly_equal(S->p + i, f, ctx))
            return 1;
    return 0;
}

static void polyset_copy(polyset_t *dst, const polyset_t *src,
                         const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < src->len; i++)
        polyset_append(dst, src->p + i, ctx);
}

/* 无序集合相等（用于子系统去重） */
static int polyset_equal_unordered(const polyset_t *A, const polyset_t *B,
                                   const nmod_mpoly_ctx_t ctx)
{
    slong i;
    if (A->len != B->len)
        return 0;
    for (i = 0; i < A->len; i++)
        if (!polyset_contains(B, A->p + i, ctx))
            return 0;
    return 1;
}

/* 删除第 i 个元素（保持顺序无关紧要，用尾部覆盖） */
static void polyset_remove(polyset_t *S, slong i,
                           const nmod_mpoly_ctx_t ctx)
{
    nmod_mpoly_swap(S->p + i, S->p + S->len - 1, ctx);
    nmod_mpoly_clear(S->p + S->len - 1, ctx);
    S->len--;
}

/* ------------------------------------------------------------------ */
/* 系统队列（DFS）与已处理列表                                          */
/* ------------------------------------------------------------------ */

typedef struct
{
    polyset_t *sys;
    slong len;
    slong alloc;
} syslist_t;

static void syslist_init(syslist_t *Q)
{
    Q->sys = NULL;
    Q->len = 0;
    Q->alloc = 0;
}

static void syslist_clear(syslist_t *Q, const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < Q->len; i++)
        polyset_clear(Q->sys + i, ctx);
    free(Q->sys);
    Q->sys = NULL;
    Q->len = Q->alloc = 0;
}

/* 压入 S 的拷贝 */
static void syslist_push(syslist_t *Q, const polyset_t *S,
                         const nmod_mpoly_ctx_t ctx)
{
    if (Q->len == Q->alloc)
    {
        Q->alloc = (Q->alloc == 0) ? 16 : 2 * Q->alloc;
        Q->sys = (polyset_t *) realloc(Q->sys, Q->alloc * sizeof(polyset_t));
    }
    polyset_init(Q->sys + Q->len);
    polyset_copy(Q->sys + Q->len, S, ctx);
    Q->len++;
}

/* 弹出栈顶（所有权转移给 *out，调用方负责 clear） */
static int syslist_pop(polyset_t *out, syslist_t *Q)
{
    if (Q->len == 0)
        return 0;
    *out = Q->sys[Q->len - 1];  /* 浅拷贝转移所有权 */
    Q->len--;
    return 1;
}

static int syslist_contains(const syslist_t *Q, const polyset_t *S,
                            const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < Q->len; i++)
        if (polyset_equal_unordered(Q->sys + i, S, ctx))
            return 1;
    return 0;
}

/* ------------------------------------------------------------------ */
/* 基本工具：类、初式、伪除                                            */
/* ------------------------------------------------------------------ */

static slong poly_class(const nmod_mpoly_t f, const nmod_mpoly_ctx_t ctx)
{
    slong n = nmod_mpoly_ctx_nvars(ctx);
    slong v;
    for (v = n - 1; v >= 0; v--)
        if (nmod_mpoly_degree_si(f, v, ctx) > 0)
            return v;
    return -1;
}

static int rank_cmp(const nmod_mpoly_t f, const nmod_mpoly_t g,
                    const nmod_mpoly_ctx_t ctx)
{
    slong cf = poly_class(f, ctx);
    slong cg = poly_class(g, ctx);
    slong df, dg;
    if (cf != cg)
        return (cf < cg) ? -1 : 1;
    if (cf < 0)
        return 0;
    df = nmod_mpoly_degree_si(f, cf, ctx);
    dg = nmod_mpoly_degree_si(g, cf, ctx);
    return (df < dg) ? -1 : (df > dg) ? 1 : 0;
}

/* 初式：f 关于主变元 x_var 的首项系数 */
static void poly_initial(nmod_mpoly_t lc, const nmod_mpoly_t f, slong var,
                         const nmod_mpoly_ctx_t ctx)
{
    nmod_mpoly_univar_t u;
    slong i, len, e, best_i = 0, best_e = -1;

    nmod_mpoly_univar_init(u, ctx);
    nmod_mpoly_to_univar(u, f, var, ctx);
    len = nmod_mpoly_univar_length(u, ctx);
    for (i = 0; i < len; i++)
    {
        e = nmod_mpoly_univar_get_term_exp_si(u, i, ctx);
        if (e > best_e)
        {
            best_e = e;
            best_i = i;
        }
    }
    if (len > 0)
        nmod_mpoly_univar_get_term_coeff(lc, u, best_i, ctx);
    else
        nmod_mpoly_zero(lc, ctx);
    nmod_mpoly_univar_clear(u, ctx);
}

/*
 * 伪除余式 r = prem(f, g, x_var)
 * 优化：init(g) 为常数时，用其逆元缩放消去项，r 不做整体乘法，
 *       避免稠密化；否则退回一般伪除。
 */
static void poly_prem(nmod_mpoly_t r, const nmod_mpoly_t f,
                      const nmod_mpoly_t g, slong var,
                      const nmod_mpoly_ctx_t ctx)
{
    nmod_mpoly_t lg, lr, t1, t2, xpow;
    slong dg, dr;
    int lg_const;
    ulong lg_inv = 1;
    ulong p = nmod_mpoly_ctx_modulus(ctx);
    nmod_t mod;

    nmod_init(&mod, p);

    dg = nmod_mpoly_degree_si(g, var, ctx);
    if (dg <= 0)
    {
        nmod_mpoly_set(r, f, ctx);
        return;
    }

    nmod_mpoly_init(lg, ctx);
    nmod_mpoly_init(lr, ctx);
    nmod_mpoly_init(t1, ctx);
    nmod_mpoly_init(t2, ctx);
    nmod_mpoly_init(xpow, ctx);

    poly_initial(lg, g, var, ctx);
    lg_const = nmod_mpoly_is_ui(lg, ctx);
    if (lg_const)
    {
        ulong c = nmod_mpoly_get_term_coeff_ui(lg, 0, ctx);
        lg_inv = nmod_inv(c, mod);
    }

    nmod_mpoly_set(r, f, ctx);

    while (!nmod_mpoly_is_zero(r, ctx) &&
           (dr = nmod_mpoly_degree_si(r, var, ctx)) >= dg)
    {
        poly_initial(lr, r, var, ctx);

        /* xpow = x_var^(dr-dg) */
        nmod_mpoly_one(xpow, ctx);
        {
            ulong *exps = (ulong *) calloc(nmod_mpoly_ctx_nvars(ctx),
                                           sizeof(ulong));
            exps[var] = (ulong)(dr - dg);
            nmod_mpoly_set_coeff_ui_ui(xpow, 1, exps, ctx);
            free(exps);
        }

        if (lg_const)
        {
            /* r <- r - lg^{-1} * init(r) * x^(dr-dg) * g */
            nmod_mpoly_scalar_mul_ui(t2, lr, lg_inv, ctx);
            nmod_mpoly_mul(t2, t2, g, ctx);
            nmod_mpoly_mul(t2, t2, xpow, ctx);
            nmod_mpoly_sub(r, r, t2, ctx);
        }
        else
        {
            nmod_mpoly_mul(t1, lg, r, ctx);
            nmod_mpoly_mul(t2, lr, g, ctx);
            nmod_mpoly_mul(t2, t2, xpow, ctx);
            nmod_mpoly_sub(r, t1, t2, ctx);
        }
    }

    nmod_mpoly_clear(lg, ctx);
    nmod_mpoly_clear(lr, ctx);
    nmod_mpoly_clear(t1, ctx);
    nmod_mpoly_clear(t2, ctx);
    nmod_mpoly_clear(xpow, ctx);
}

static void poly_prem_chain(nmod_mpoly_t r, const nmod_mpoly_t f,
                            const polyset_t *B, const nmod_mpoly_ctx_t ctx)
{
    slong i;
    nmod_mpoly_t tmp;
    nmod_mpoly_init(tmp, ctx);
    nmod_mpoly_set(r, f, ctx);
    for (i = B->len - 1; i >= 0; i--)
    {
        slong c = poly_class(B->p + i, ctx);
        if (c < 0)
            continue;
        poly_prem(tmp, r, B->p + i, c, ctx);
        nmod_mpoly_set(r, tmp, ctx);
    }
    nmod_mpoly_clear(tmp, ctx);
}

/* ------------------------------------------------------------------ */
/* x^p = x 指数约化（只求 F_p 有理点时保值）                            */
/* ------------------------------------------------------------------ */

static void field_reduce_exponents(nmod_mpoly_t g, const nmod_mpoly_t f,
                                   const nmod_mpoly_ctx_t ctx)
{
    slong n = nmod_mpoly_ctx_nvars(ctx);
    slong i, v, len = nmod_mpoly_length(f, ctx);
    ulong p = nmod_mpoly_ctx_modulus(ctx);
    ulong *exps = (ulong *) malloc(n * sizeof(ulong));
    nmod_mpoly_t acc;

    nmod_mpoly_init(acc, ctx);
    nmod_mpoly_zero(acc, ctx);

    for (i = 0; i < len; i++)
    {
        ulong c = nmod_mpoly_get_term_coeff_ui(f, i, ctx);
        ulong c_old;
        nmod_mpoly_get_term_exp_ui(exps, f, i, ctx);
        for (v = 0; v < n; v++)
            if (exps[v] >= p)   /* e >= 1 时 x^e = x^{((e-1) mod (p-1)) + 1} */
                exps[v] = (exps[v] - 1) % (p - 1) + 1;
        c_old = nmod_mpoly_get_coeff_ui_ui(acc, exps, ctx);
        nmod_mpoly_set_coeff_ui_ui(acc, (c_old + c) % p, exps, ctx);
    }
    nmod_mpoly_swap(g, acc, ctx);
    nmod_mpoly_clear(acc, ctx);
    free(exps);
}

/* ------------------------------------------------------------------ */
/* 因式分解分裂                                                        */
/* ------------------------------------------------------------------ */

static slong g_stat_systems = 0, g_stat_splits = 0, g_stat_charsets = 0;

/*
 * 取 f 的互异不可约因子（丢弃重数与常数因子），存入 bases。
 * 分解失败时退化为 bases = {f}。
 */
static void distinct_factors(polyset_t *bases, const nmod_mpoly_t f,
                             const nmod_mpoly_ctx_t ctx)
{
    nmod_mpoly_factor_t fac;
    slong i, nf;

    nmod_mpoly_factor_init(fac, ctx);
    if (nmod_mpoly_factor(fac, f, ctx))
    {
        nmod_mpoly_t b;
        nmod_mpoly_init(b, ctx);
        nf = nmod_mpoly_factor_length(fac, ctx);
        for (i = 0; i < nf; i++)
        {
            nmod_mpoly_factor_get_base(b, fac, i, ctx);
            if (!nmod_mpoly_is_ui(b, ctx) && !polyset_contains(bases, b, ctx))
                polyset_append(bases, b, ctx);
        }
        nmod_mpoly_clear(b, ctx);
    }
    else
    {
        polyset_append(bases, f, ctx);
    }
    nmod_mpoly_factor_clear(fac, ctx);
}

enum { SYS_OK = 0, SYS_CONTRA = 1, SYS_SPLIT = 2 };

/*
 * 系统规范化：
 *   - 删除零多项式；非零常数 => 矛盾
 *   - 可选 x^p=x 指数约化
 *   - 每个多项式做不可约分解：
 *       单因子   => 用无平方因子替换原式
 *       多因子   => 系统按因子分裂为子系统入队（完整分解树的核心步骤）
 *       因子过多 => 用互异因子之积（无平方部分）替换，不分裂
 */
static int normalize_system(polyset_t *P, syslist_t *Q, int field_reduce,
                            const nmod_mpoly_ctx_t ctx)
{
    slong i, j;

    for (i = 0; i < P->len; )
    {
        polyset_t bases;

        if (nmod_mpoly_is_zero(P->p + i, ctx))
        {
            polyset_remove(P, i, ctx);
            continue;
        }
        if (nmod_mpoly_is_ui(P->p + i, ctx))
            return SYS_CONTRA;

        if (field_reduce)
        {
            field_reduce_exponents(P->p + i, P->p + i, ctx);
            if (nmod_mpoly_is_zero(P->p + i, ctx))
            {
                polyset_remove(P, i, ctx);
                continue;
            }
            if (nmod_mpoly_is_ui(P->p + i, ctx))
                return SYS_CONTRA;
        }

        polyset_init(&bases);
        distinct_factors(&bases, P->p + i, ctx);

        if (bases.len == 0)     /* 只剩常数因子：非零常数 => 矛盾 */
        {
            polyset_clear(&bases, ctx);
            return SYS_CONTRA;
        }
        else if (bases.len == 1)
        {
            nmod_mpoly_set(P->p + i, bases.p, ctx);
            i++;
        }
        else if (bases.len <= MAX_SPLIT_FACTORS)
        {
            /* 分裂：Zero(P ∪ {∏ b_j}) = ⋃_j Zero(P ∪ {b_j}) */
            for (j = 0; j < bases.len; j++)
            {
                nmod_mpoly_set(P->p + i, bases.p + j, ctx);
                syslist_push(Q, P, ctx);
            }
            g_stat_splits++;
            polyset_clear(&bases, ctx);
            return SYS_SPLIT;
        }
        else
        {
            /* 因子过多：只取无平方部分，避免分支爆炸 */
            nmod_mpoly_set(P->p + i, bases.p, ctx);
            for (j = 1; j < bases.len; j++)
                nmod_mpoly_mul(P->p + i, P->p + i, bases.p + j, ctx);
            i++;
        }
        polyset_clear(&bases, ctx);
    }

    /* 集合内去重 */
    for (i = 0; i < P->len; i++)
        for (j = P->len - 1; j > i; j--)
            if (nmod_mpoly_equal(P->p + i, P->p + j, ctx))
                polyset_remove(P, j, ctx);

    return SYS_OK;
}

/* ------------------------------------------------------------------ */
/* 基列与特征列（余式即时分解，必要时分裂系统）                          */
/* ------------------------------------------------------------------ */

static void basic_set(polyset_t *B, const polyset_t *P,
                      const nmod_mpoly_ctx_t ctx)
{
    slong last_class = -1;

    while (1)
    {
        slong i, best = -1;

        for (i = 0; i < P->len; i++)
        {
            const nmod_mpoly_struct *f = P->p + i;
            slong cf = poly_class(f, ctx);
            slong j;
            int reduced = 1;

            if (nmod_mpoly_is_zero(f, ctx))
                continue;
            if (B->len > 0 && cf <= last_class)
                continue;

            for (j = 0; j < B->len; j++)
            {
                slong cj = poly_class(B->p + j, ctx);
                if (cj >= 0 &&
                    nmod_mpoly_degree_si(f, cj, ctx) >=
                        nmod_mpoly_degree_si(B->p + j, cj, ctx))
                {
                    reduced = 0;
                    break;
                }
            }
            if (!reduced)
                continue;

            if (best < 0 || rank_cmp(f, P->p + best, ctx) < 0)
                best = i;
        }

        if (best < 0)
            break;

        polyset_append(B, P->p + best, ctx);
        last_class = poly_class(P->p + best, ctx);
        if (last_class < 0)
            break;
    }
}

/*
 * 特征列计算（带分裂）：
 *   工作集 P 上迭代取基列 B，对余集做伪除；
 *   每个非零余式 r 先做不可约分解：
 *     常数        => 矛盾（r ∈ ideal(P)）
 *     单因子      => 加入工作集
 *     多因子      => 系统分裂入队，本分支终止（SYS_SPLIT）
 * 正常收敛时 CS = B。
 */
static int char_set_split(polyset_t *CS, const polyset_t *F, syslist_t *Q,
                          const nmod_mpoly_ctx_t ctx)
{
    polyset_t P;
    nmod_mpoly_t r;
    slong i, j, round = 0;
    int ret = SYS_OK;

    polyset_init(&P);
    nmod_mpoly_init(r, ctx);
    for (i = 0; i < F->len; i++)
        if (!polyset_contains(&P, F->p + i, ctx))
            polyset_append(&P, F->p + i, ctx);

    while (1)
    {
        int has_new = 0;

        for (i = 0; i < CS->len; i++)
            nmod_mpoly_clear(CS->p + i, ctx);
        CS->len = 0;

        basic_set(CS, &P, ctx);
        g_stat_charsets++;

        if (CS->len > 0 && poly_class(CS->p, ctx) < 0)
        {
            ret = SYS_CONTRA;
            goto done;
        }

        for (i = 0; i < P.len; i++)
        {
            int in_B = 0;
            for (j = 0; j < CS->len; j++)
                if (nmod_mpoly_equal(P.p + i, CS->p + j, ctx))
                {
                    in_B = 1;
                    break;
                }
            if (in_B)
                continue;

            poly_prem_chain(r, P.p + i, CS, ctx);
            if (nmod_mpoly_is_zero(r, ctx))
                continue;
            if (nmod_mpoly_is_ui(r, ctx))   /* 非零常数 ∈ ideal(P)：矛盾 */
            {
                ret = SYS_CONTRA;
                goto done;
            }

            {
                polyset_t bases;
                int any_in = 0;
                polyset_init(&bases);
                distinct_factors(&bases, r, ctx);
                for (j = 0; j < bases.len; j++)
                    if (polyset_contains(&P, bases.p + j, ctx))
                        any_in = 1;

                if (bases.len == 0)
                {
                    polyset_clear(&bases, ctx);
                    ret = SYS_CONTRA;
                    goto done;
                }
                else if (any_in)
                {
                    /* r ∈ ideal(P) 且其某因子已在 P 中：
                       零点集无新信息。跳过，不分裂（否则子系统与
                       当前系统相同，会被去重丢弃导致漏解）。
                       此时链可能提前收敛为“弱特征列”，但 CS ⊆ P
                       保证 Zero(P) ⊆ Zero(CS)，枚举+验证仍然完备。 */
                }
                else if (bases.len == 1)
                {
                    polyset_append(&P, bases.p, ctx);
                    has_new = 1;
                }
                else if (bases.len <= MAX_SPLIT_FACTORS)
                {
                    /* Zero(P) = Zero(P ∪ {r}) = ⋃_j Zero(P ∪ {b_j})，分裂 */
                    for (j = 0; j < bases.len; j++)
                    {
                        polyset_t child;
                        polyset_init(&child);
                        polyset_copy(&child, &P, ctx);
                        polyset_append(&child, bases.p + j, ctx);
                        syslist_push(Q, &child, ctx);
                        polyset_clear(&child, ctx);
                    }
                    g_stat_splits++;
                    polyset_clear(&bases, ctx);
                    ret = SYS_SPLIT;
                    goto done;
                }
                else
                {
                    nmod_mpoly_t sf;
                    nmod_mpoly_init(sf, ctx);
                    nmod_mpoly_set(sf, bases.p, ctx);
                    for (j = 1; j < bases.len; j++)
                        nmod_mpoly_mul(sf, sf, bases.p + j, ctx);
                    if (!polyset_contains(&P, sf, ctx))
                    {
                        polyset_append(&P, sf, ctx);
                        has_new = 1;
                    }
                    nmod_mpoly_clear(sf, ctx);
                }
                polyset_clear(&bases, ctx);
            }
        }

        if (!has_new)
            break;
        if (++round > 500)
        {
            fprintf(stderr, "warning: charset iteration limit reached\n");
            break;
        }
    }

done:
    polyset_clear(&P, ctx);
    nmod_mpoly_clear(r, ctx);
    return ret;
}

/* ------------------------------------------------------------------ */
/* 解列表与三角列回代                                                  */
/* ------------------------------------------------------------------ */

typedef struct
{
    ulong *vals;
    slong count;
    slong alloc;
    slong nvars;
} sol_list_t;

static void sol_list_init(sol_list_t *L, slong nvars)
{
    L->vals = NULL;
    L->count = 0;
    L->alloc = 0;
    L->nvars = nvars;
}

static void sol_list_clear(sol_list_t *L)
{
    free(L->vals);
    L->vals = NULL;
    L->count = L->alloc = 0;
}

static void sol_list_add_unique(sol_list_t *L, const ulong *sol)
{
    slong i;
    for (i = 0; i < L->count; i++)
        if (memcmp(L->vals + i * L->nvars, sol,
                   L->nvars * sizeof(ulong)) == 0)
            return;
    if (L->count == L->alloc)
    {
        L->alloc = (L->alloc == 0) ? 16 : 2 * L->alloc;
        L->vals = (ulong *) realloc(L->vals,
                                    L->alloc * L->nvars * sizeof(ulong));
    }
    memcpy(L->vals + L->count * L->nvars, sol, L->nvars * sizeof(ulong));
    L->count++;
}

static int check_solution(const polyset_t *F, const ulong *sol,
                          const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < F->len; i++)
        if (nmod_mpoly_evaluate_all_ui(F->p + i, (ulong *) sol, ctx) != 0)
            return 0;
    return 1;
}

static void mpoly_to_nmod_poly(nmod_poly_t up, const nmod_mpoly_t f,
                               slong var, const nmod_mpoly_ctx_t ctx)
{
    slong n = nmod_mpoly_ctx_nvars(ctx);
    slong i, len = nmod_mpoly_length(f, ctx);
    ulong *exps = (ulong *) malloc(n * sizeof(ulong));

    nmod_poly_zero(up);
    for (i = 0; i < len; i++)
    {
        ulong c = nmod_mpoly_get_term_coeff_ui(f, i, ctx);
        nmod_mpoly_get_term_exp_ui(exps, f, i, ctx);
        nmod_poly_set_coeff_ui(up, (slong) exps[var], c);
    }
    free(exps);
}

/* 一元多项式在 F_p 中的全部根（因式分解取一次因子） */
static slong wu_poly_roots(ulong *roots, const nmod_poly_t f)
{
    nmod_poly_factor_t fac;
    slong i, nroots = 0;

    if (nmod_poly_degree(f) < 1)
        return 0;

    nmod_poly_factor_init(fac);
    nmod_poly_factor(fac, f);
    for (i = 0; i < fac->num; i++)
    {
        const nmod_poly_struct *g = fac->p + i;
        if (nmod_poly_degree(g) == 1)
        {
            ulong b = nmod_poly_get_coeff_ui(g, 0);
            ulong a = nmod_poly_get_coeff_ui(g, 1);
            roots[nroots++] = nmod_mul(nmod_neg(b, f->mod),
                                       nmod_inv(a, f->mod), f->mod);
        }
    }
    nmod_poly_factor_clear(fac);
    return nroots;
}

static void enumerate_zeros(const polyset_t *CS, const polyset_t *F,
                            sol_list_t *out, ulong *sol, slong var,
                            const nmod_mpoly_ctx_t ctx)
{
    slong n = nmod_mpoly_ctx_nvars(ctx);
    ulong p = nmod_mpoly_ctx_modulus(ctx);
    slong i, k;
    nmod_mpoly_t sub;
    const nmod_mpoly_struct *pivot = NULL;

    if (var == n)
    {
        if (check_solution(F, sol, ctx))
            sol_list_add_unique(out, sol);
        return;
    }

    for (i = 0; i < CS->len; i++)
        if (poly_class(CS->p + i, ctx) == var)
        {
            pivot = CS->p + i;
            break;
        }

    nmod_mpoly_init(sub, ctx);

    if (pivot != NULL)
    {
        slong j;
        nmod_mpoly_t tmp;
        nmod_mpoly_init(tmp, ctx);
        nmod_mpoly_set(sub, pivot, ctx);
        for (j = 0; j < var; j++)
        {
            nmod_mpoly_evaluate_one_ui(tmp, sub, j, sol[j], ctx);
            nmod_mpoly_swap(sub, tmp, ctx);
        }
        nmod_mpoly_clear(tmp, ctx);

        if (nmod_mpoly_is_zero(sub, ctx))
        {
            pivot = NULL;       /* 初式退化：转自由变元 */
        }
        else if (poly_class(sub, ctx) < 0)
        {
            nmod_mpoly_clear(sub, ctx);
            return;             /* 非零常数：无解分支 */
        }
        else
        {
            nmod_poly_t up;
            ulong *roots;
            slong nroots, deg;

            nmod_poly_init(up, p);
            mpoly_to_nmod_poly(up, sub, var, ctx);
            deg = nmod_poly_degree(up);
            roots = (ulong *) malloc((deg > 0 ? deg : 1) * sizeof(ulong));
            nroots = wu_poly_roots(roots, up);
            for (k = 0; k < nroots; k++)
            {
                sol[var] = roots[k];
                enumerate_zeros(CS, F, out, sol, var + 1, ctx);
            }
            free(roots);
            nmod_poly_clear(up);
        }
    }

    if (pivot == NULL)
    {
        if (p <= FREE_VAR_ENUM_LIMIT)
        {
            ulong v;
            for (v = 0; v < p; v++)
            {
                sol[var] = v;
                enumerate_zeros(CS, F, out, sol, var + 1, ctx);
            }
        }
        else
        {
            fprintf(stderr,
                    "warning: x%ld 为自由变元且 p=%lu 过大，跳过穷举\n",
                    (long) var, (unsigned long) p);
        }
    }

    nmod_mpoly_clear(sub, ctx);
}

/* ------------------------------------------------------------------ */
/* 队列驱动的完整吴分解求解器                                          */
/* ------------------------------------------------------------------ */

static void print_polyset(const char *title, const polyset_t *S,
                          const char **vars, const nmod_mpoly_ctx_t ctx)
{
    slong i;
    printf("%s\n", title);
    for (i = 0; i < S->len; i++)
    {
        char *s = nmod_mpoly_get_str_pretty(S->p + i, vars, ctx);
        printf("  [%ld] %s\n", (long) i + 1, s);
        flint_free(s);
    }
}

static void wu_solve(const polyset_t *F_orig, sol_list_t *out,
                     int field_reduce, const char **vars,
                     const nmod_mpoly_ctx_t ctx)
{
    syslist_t queue, processed;
    polyset_t P;
    slong n = nmod_mpoly_ctx_nvars(ctx);
    slong ncomp = 0;

    syslist_init(&queue);
    syslist_init(&processed);
    syslist_push(&queue, F_orig, ctx);

    while (syslist_pop(&P, &queue))
    {
        polyset_t CS;
        int st;
        slong i;

        if (g_stat_systems >= MAX_SYSTEMS)
        {
            fprintf(stderr, "warning: 子系统数达到上限 %d，提前停止\n",
                    MAX_SYSTEMS);
            polyset_clear(&P, ctx);
            break;
        }

        if (syslist_contains(&processed, &P, ctx))   /* 去重 */
        {
            polyset_clear(&P, ctx);
            continue;
        }
        syslist_push(&processed, &P, ctx);
        g_stat_systems++;

        st = normalize_system(&P, &queue, field_reduce, ctx);
        if (st != SYS_OK)
        {
            polyset_clear(&P, ctx);
            continue;
        }
        if (P.len == 0)          /* 空系统：全空间，稀有情形 */
        {
            polyset_clear(&P, ctx);
            continue;
        }

        polyset_init(&CS);
        st = char_set_split(&CS, &P, &queue, ctx);
        if (st != SYS_OK)
        {
            polyset_clear(&CS, ctx);
            polyset_clear(&P, ctx);
            continue;
        }

        ncomp++;
        if (ncomp <= PRINT_COMPONENT_LIMIT)
        {
            char title[64];
            snprintf(title, sizeof(title), "分支 #%ld 的特征列:",
                     (long) ncomp);
            print_polyset(title, &CS, vars, ctx);
        }

        /* 主分支：枚举 Zero(CS)，代回原系统验证 */
        {
            ulong *sol = (ulong *) calloc(n, sizeof(ulong));
            enumerate_zeros(&CS, F_orig, out, sol, 0, ctx);
            free(sol);
        }

        /* 初式分支：Zero(F) ⊇ Zero(F ∪ CS ∪ {I_i}) 补漏 */
        for (i = 0; i < CS.len; i++)
        {
            slong c = poly_class(CS.p + i, ctx);
            nmod_mpoly_t I;

            if (c < 0)
                continue;
            nmod_mpoly_init(I, ctx);
            poly_initial(I, CS.p + i, c, ctx);
            if (!nmod_mpoly_is_ui(I, ctx))
            {
                polyset_t child;
                slong j;
                polyset_init(&child);
                polyset_copy(&child, &P, ctx);
                for (j = 0; j < CS.len; j++)
                    if (!polyset_contains(&child, CS.p + j, ctx))
                        polyset_append(&child, CS.p + j, ctx);
                polyset_append(&child, I, ctx);
                if (!syslist_contains(&processed, &child, ctx))
                    syslist_push(&queue, &child, ctx);
                polyset_clear(&child, ctx);
            }
            nmod_mpoly_clear(I, ctx);
        }

        polyset_clear(&CS, ctx);
        polyset_clear(&P, ctx);
    }

    syslist_clear(&queue, ctx);
    syslist_clear(&processed, ctx);
}

/* ------------------------------------------------------------------ */
/* 主程序                                                              */
/* ------------------------------------------------------------------ */

static int is_prime_ui(ulong n)
{
    ulong d;
    if (n < 2)
        return 0;
    if (n % 2 == 0)
        return n == 2;
    for (d = 3; d * d <= n; d += 2)
        if (n % d == 0)
            return 0;
    return 1;
}

int main(int argc, char **argv)
{
    const char *vars[] = { "x", "y", "z" };
    slong nvars = 3;
    ulong p = 13;
    ulong k = 1;
    int field_reduce = 0;
    int npos = 0;
    int i;

    for (i = 1; i < argc; i++)
    {
        if (strcmp(argv[i], "-f") == 0)
            field_reduce = 1;
        else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0)
        {
            printf("用法: %s [k] [p] [-f]\n"
                   "  k : x^k + y^k + z^k - 5 中的指数 (默认 1)\n"
                   "  p : 素数模 (默认 13)\n"
                   "  -f: 开启 x^p = x 指数约化 (只求 F_p 有理点时保值)\n",
                   argv[0]);
            return 0;
        }
        else
        {
            ulong v = strtoul(argv[i], NULL, 10);
            if (npos == 0)
                k = v;
            else if (npos == 1)
                p = v;
            npos++;
        }
    }

    if (k == 0)
        k = 1;
    if (!is_prime_ui(p))
    {
        fprintf(stderr, "错误: p = %lu 不是素数\n", (unsigned long) p);
        return 1;
    }

    {
        nmod_mpoly_ctx_t ctx;
        polyset_t F;
        sol_list_t sols;
        nmod_mpoly_t f;
        slong j;
        clock_t t0, t1;

        nmod_mpoly_ctx_init(ctx, nvars, ORD_LEX, p);
        polyset_init(&F);
        sol_list_init(&sols, nvars);

        printf("======  吴特征列方法（完整分解树） / F_%lu, k=%lu%s ======\n",
               (unsigned long) p, (unsigned long) k,
               field_reduce ? ", 指数约化开" : "");
        printf("变元序: x < y < z\n");

        /* f1 = x^k + y^k + z^k - 5 （程序化构造，k 可以很大） */
        nmod_mpoly_init(f, ctx);
        {
            ulong *exps = (ulong *) calloc(nvars, sizeof(ulong));
            nmod_mpoly_zero(f, ctx);
            for (j = 0; j < nvars; j++)
            {
                memset(exps, 0, nvars * sizeof(ulong));
                exps[j] = k;
                nmod_mpoly_set_coeff_ui_ui(f, 1, exps, ctx);
            }
            memset(exps, 0, nvars * sizeof(ulong));
            nmod_mpoly_set_coeff_ui_ui(f, (p - 5 % p) % p, exps, ctx);
            free(exps);
        }
        polyset_append(&F, f, ctx);

        /* f2, f3 */
        nmod_mpoly_set_str_pretty(f, "x*y + y*z + z*x - 8", vars, ctx);
        polyset_append(&F, f, ctx);
        nmod_mpoly_set_str_pretty(f, "x*y*z - 4", vars, ctx);
        polyset_append(&F, f, ctx);
        nmod_mpoly_clear(f, ctx);

        print_polyset("输入系统 F:", &F, vars, ctx);

        t0 = clock();
        wu_solve(&F, &sols, field_reduce, vars, ctx);
        t1 = clock();

        printf("\nF_%lu 上的解 (共 %ld 组):\n",
               (unsigned long) p, (long) sols.count);
        for (j = 0; j < sols.count; j++)
        {
            slong v;
            printf("  (");
            for (v = 0; v < nvars; v++)
                printf("%s=%lu%s", vars[v],
                       (unsigned long) sols.vals[j * nvars + v],
                       v + 1 < nvars ? ", " : "");
            printf(")\n");
        }

        printf("\n统计: 处理子系统 %ld 个, 分裂 %ld 次, 特征列迭代 %ld 轮, "
               "耗时 %.3f s\n",
               (long) g_stat_systems, (long) g_stat_splits,
               (long) g_stat_charsets,
               (double) (t1 - t0) / CLOCKS_PER_SEC);

        sol_list_clear(&sols);
        polyset_clear(&F, ctx);
        nmod_mpoly_ctx_clear(ctx);
    }
    return 0;
}
