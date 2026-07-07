/*
 * wu_charset.c
 *
 * 有限域 F_p 上多项式系统的吴特征列（Wu's characteristic set）方法求解
 * 基于 FLINT 库（nmod_mpoly：小素数模 p 的多元多项式）
 *
 * 算法框架：
 *   1. 变元排序 x0 < x1 < ... < x{n-1}（类 class = 最高出现变元的下标）
 *   2. 基列（basic set）选取：从多项式集合中取秩最小的约化升列
 *   3. 对余下多项式关于基列做逐次伪除（pseudo-remainder），
 *      非零余式加入集合，迭代直到全部余式为零 => 得到特征列 CS
 *   4. 零点分解定理：
 *         Zero(F) = Zero(CS / J)  ∪  ⋃_i Zero(F ∪ CS ∪ {I_i})
 *      其中 I_i 为特征列各元素的初式（initial），J = ∏ I_i。
 *      程序对每个分支递归计算特征列，并对三角列自下而上回代、
 *      用 nmod_poly 因式分解求单变元根，枚举出候选解，
 *      最后代回原系统 F 验证，去重后输出全部解。
 *
 * 编译（需要 FLINT >= 3.0，2.8/2.9 亦兼容本文件用到的 API）：
 *   gcc -O2 -o wu_charset wu_charset.c -lflint -lgmp
 *   （某些发行版还需 -lmpfr）
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/nmod_mpoly.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_poly_factor.h>
#include <flint/nmod.h>
/* ------------------------------------------------------------------ */
/* 动态多项式集合                                                      */
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

/* 追加 f 的一份拷贝 */
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

/* 集合中是否已有相同多项式（避免迭代时重复加入） */
static int polyset_contains(const polyset_t *S, const nmod_mpoly_t f,
                            const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < S->len; i++)
        if (nmod_mpoly_equal(S->p + i, f, ctx))
            return 1;
    return 0;
}

/* ------------------------------------------------------------------ */
/* 基本工具：类、主变元次数、初式、伪除                                */
/* ------------------------------------------------------------------ */

/* 类 cls(f)：f 中出现的最高变元下标；常数多项式返回 -1 */
static slong poly_class(const nmod_mpoly_t f, const nmod_mpoly_ctx_t ctx)
{
    slong n = nmod_mpoly_ctx_nvars(ctx);
    slong v;
    for (v = n - 1; v >= 0; v--)
        if (nmod_mpoly_degree_si(f, v, ctx) > 0)
            return v;
    return -1;
}

/* 秩比较：先比类，类相同比主变元次数。返回 <0, 0, >0 */
static int rank_cmp(const nmod_mpoly_t f, const nmod_mpoly_t g,
                    const nmod_mpoly_ctx_t ctx)
{
    slong cf = poly_class(f, ctx);
    slong cg = poly_class(g, ctx);
    slong df, dg;
    if (cf != cg)
        return (cf < cg) ? -1 : 1;
    if (cf < 0)
        return 0;               /* 两个常数秩相同 */
    df = nmod_mpoly_degree_si(f, cf, ctx);
    dg = nmod_mpoly_degree_si(g, cf, ctx);
    return (df < dg) ? -1 : (df > dg) ? 1 : 0;
}

/*
 * 初式 init(f)：f 视为主变元 x_var 的一元多项式时的首项系数
 * （属于 F_p[x0,...,x_{var-1}]）
 */
static void poly_initial(nmod_mpoly_t lc, const nmod_mpoly_t f, slong var,
                         const nmod_mpoly_ctx_t ctx)
{
    nmod_mpoly_univar_t u;
    slong i, len, e, best_i = 0, best_e = -1;

    nmod_mpoly_univar_init(u, ctx);
    nmod_mpoly_to_univar(u, f, var, ctx);
    len = nmod_mpoly_univar_length(u, ctx);

    for (i = 0; i < len; i++)      /* 稳妥起见扫描最大指数项 */
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
 *
 * 逐步消去：当 deg_x(r) >= deg_x(g) 时
 *     r <- init(g) * r - init_x(r) * x^(dr-dg) * g
 * 每步 r 关于 x_var 的次数严格下降，保证终止。
 * （与经典 prem 相差 init(g) 的幂次因子，不影响零点集分析。）
 */
static void poly_prem(nmod_mpoly_t r, const nmod_mpoly_t f,
                      const nmod_mpoly_t g, slong var,
                      const nmod_mpoly_ctx_t ctx)
{
    nmod_mpoly_t lg, lr, t1, t2, xpow;
    slong dg, dr;

    dg = nmod_mpoly_degree_si(g, var, ctx);
    if (dg <= 0)
    {
        /* g 不含主变元时按约定不做伪除 */
        nmod_mpoly_set(r, f, ctx);
        return;
    }

    nmod_mpoly_init(lg, ctx);
    nmod_mpoly_init(lr, ctx);
    nmod_mpoly_init(t1, ctx);
    nmod_mpoly_init(t2, ctx);
    nmod_mpoly_init(xpow, ctx);

    poly_initial(lg, g, var, ctx);
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

        nmod_mpoly_mul(t1, lg, r, ctx);      /* t1 = init(g) * r        */
        nmod_mpoly_mul(t2, lr, g, ctx);      /* t2 = init(r) * g        */
        nmod_mpoly_mul(t2, t2, xpow, ctx);   /* t2 *= x^(dr-dg)         */
        nmod_mpoly_sub(r, t1, t2, ctx);      /* 首项相消，次数下降       */
    }

    nmod_mpoly_clear(lg, ctx);
    nmod_mpoly_clear(lr, ctx);
    nmod_mpoly_clear(t1, ctx);
    nmod_mpoly_clear(t2, ctx);
    nmod_mpoly_clear(xpow, ctx);
}

/* 对升列 B 逐次伪除：r = prem(...prem(prem(f, B_k), B_{k-1})..., B_1) */
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
/* 基列与特征列                                                        */
/* ------------------------------------------------------------------ */

/*
 * 基列（basic set）：
 *   B1 = P 中秩最小的多项式；
 *   B_{i+1} = P 中类 > cls(B_i) 且关于 B_1..B_i 均约化
 *             （即对每个 B_j，其主变元次数低于 B_j）的秩最小者。
 * 得到一个约化升列。
 */
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
                continue;       /* 升列要求类严格递增 */

            /* 关于已选元素约化：对每个 B_j，deg_{x_{cls(B_j)}}(f) < deg(B_j) */
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
        if (last_class < 0)     /* 选到非零常数：矛盾列，直接结束 */
            break;
    }
}

/*
 * 吴特征列主循环：
 *   P <- F
 *   repeat:
 *     B <- basic_set(P)
 *     R <- { prem(f, B) != 0 : f ∈ P \ B }
 *     若 R 为空则 CS = B；否则 P <- P ∪ R
 * 返回 0 正常；返回 1 表示特征列含非零常数（该分支无解）。
 */
static int char_set(polyset_t *CS, const polyset_t *F,
                    const nmod_mpoly_ctx_t ctx)
{
    polyset_t P;
    nmod_mpoly_t r;
    slong i, round = 0;

    polyset_init(&P);
    nmod_mpoly_init(r, ctx);

    for (i = 0; i < F->len; i++)
        if (!nmod_mpoly_is_zero(F->p + i, ctx) &&
            !polyset_contains(&P, F->p + i, ctx))
            polyset_append(&P, F->p + i, ctx);

    while (1)
    {
        int has_new = 0;

        for (i = 0; i < CS->len; i++)
            nmod_mpoly_clear(CS->p + i, ctx);
        CS->len = 0;

        basic_set(CS, &P, ctx);

        /* 基列含非零常数 => 1 ∈ 理想，系统矛盾 */
        if (CS->len > 0 && poly_class(CS->p, ctx) < 0)
        {
            polyset_clear(&P, ctx);
            nmod_mpoly_clear(r, ctx);
            return 1;
        }

        for (i = 0; i < P.len; i++)
        {
            slong j;
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
            if (!nmod_mpoly_is_zero(r, ctx) && !polyset_contains(&P, r, ctx))
            {
                if (poly_class(r, ctx) < 0)   /* 余式为非零常数：矛盾 */
                {
                    polyset_clear(&P, ctx);
                    nmod_mpoly_clear(r, ctx);
                    return 1;
                }
                polyset_append(&P, r, ctx);
                has_new = 1;
            }
        }

        if (!has_new)
            break;

        if (++round > 200)      /* 保险阈值，理论上必终止 */
        {
            fprintf(stderr, "warning: charset iteration limit reached\n");
            break;
        }
    }

    polyset_clear(&P, ctx);
    nmod_mpoly_clear(r, ctx);
    return 0;
}

/* ------------------------------------------------------------------ */
/* 三角列回代求解（枚举 F_p 中的零点）                                  */
/* ------------------------------------------------------------------ */

typedef struct
{
    ulong *vals;                /* 扁平存放：每 nvars 个为一组解 */
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

/* 解是否满足整个系统 F */
static int check_solution(const polyset_t *F, const ulong *sol,
                          const nmod_mpoly_ctx_t ctx)
{
    slong i;
    for (i = 0; i < F->len; i++)
        if (nmod_mpoly_evaluate_all_ui(F->p + i, (ulong *) sol, ctx) != 0)
            return 0;
    return 1;
}

/* 把仅含变元 var 的 mpoly 转成一元 nmod_poly */
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

/* 求一元多项式在 F_p 中的全部根（通过因式分解取一次因子） */
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
            /* g = a*x + b，根 = -b * a^{-1} mod p */
            ulong b = nmod_poly_get_coeff_ui(g, 0);
            ulong a = nmod_poly_get_coeff_ui(g, 1);
            ulong r = nmod_mul(nmod_neg(b, f->mod),
                               nmod_inv(a, f->mod), f->mod);
            roots[nroots++] = r;
        }
    }
    nmod_poly_factor_clear(fac);
    return nroots;
}

/*
 * 沿三角列自下而上回代枚举解。
 *   var  : 当前处理的变元下标（从 0 递增）
 *   sol  : 已确定的部分解
 * 若某变元不是任何列元素的类（欠定 / 初式退化），当 p 较小时穷举该变元。
 */
#define FREE_VAR_ENUM_LIMIT 4096

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
        if (check_solution(F, sol, ctx))   /* 代回原系统验证 */
            sol_list_add_unique(out, sol);
        return;
    }

    /* 找类恰为 var 的列元素 */
    for (i = 0; i < CS->len; i++)
        if (poly_class(CS->p + i, ctx) == var)
        {
            pivot = CS->p + i;
            break;
        }

    nmod_mpoly_init(sub, ctx);

    if (pivot != NULL)
    {
        /* 代入 x0..x{var-1} 的已知值，得到 x_var 的一元多项式 */
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
            pivot = NULL;       /* 初式退化，多项式恒为零：转为自由变元 */
        }
        else if (poly_class(sub, ctx) < 0)
        {
            /* 变成非零常数：该分支无解 */
            nmod_mpoly_clear(sub, ctx);
            return;
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
        /* 自由变元：小域时穷举 */
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
                    "warning: x%ld 为自由变元且 p=%lu 过大，跳过穷举 "
                    "(解集可能为正维数)\n", (long) var, (unsigned long) p);
        }
    }

    nmod_mpoly_clear(sub, ctx);
}

/* ------------------------------------------------------------------ */
/* 吴零点分解：Zero(F) = Zero(CS/J) ∪ ⋃ Zero(F ∪ CS ∪ {I_i})           */
/* ------------------------------------------------------------------ */

#define MAX_DECOMP_DEPTH 12

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

static void wu_solve_rec(const polyset_t *F_orig, const polyset_t *F_cur,
                         sol_list_t *out, slong depth, const char **vars,
                         const nmod_mpoly_ctx_t ctx)
{
    polyset_t CS;
    slong n = nmod_mpoly_ctx_nvars(ctx);
    slong i;
    ulong *sol;

    if (depth > MAX_DECOMP_DEPTH)
        return;

    polyset_init(&CS);
    if (char_set(&CS, F_cur, ctx) != 0)
    {
        if (depth == 0)
            printf("特征列含非零常数：系统在 F_p 上无解。\n");
        polyset_clear(&CS, ctx);
        return;
    }

    if (depth == 0)
        print_polyset("特征列 CS:", &CS, vars, ctx);

    /* 主分支：枚举 Zero(CS)，逐一代回原系统 F 验证（自动涵盖 Zero(CS/J)） */
    sol = (ulong *) calloc(n, sizeof(ulong));
    enumerate_zeros(&CS, F_orig, out, sol, 0, ctx);
    free(sol);

    /* 分支：对每个非平凡初式 I_i，递归求解 F ∪ CS ∪ {I_i}，
       补回主分支中因初式为零而漏掉的解 */
    for (i = 0; i < CS.len; i++)
    {
        slong c = poly_class(CS.p + i, ctx);
        nmod_mpoly_t I;

        if (c < 0)
            continue;
        nmod_mpoly_init(I, ctx);
        poly_initial(I, CS.p + i, c, ctx);

        if (!nmod_mpoly_is_ui(I, ctx))   /* 初式非常数才需要分支 */
        {
            polyset_t Fb;
            slong j;
            polyset_init(&Fb);
            for (j = 0; j < F_cur->len; j++)
                polyset_append(&Fb, F_cur->p + j, ctx);
            for (j = 0; j < CS.len; j++)
                if (!polyset_contains(&Fb, CS.p + j, ctx))
                    polyset_append(&Fb, CS.p + j, ctx);
            if (!polyset_contains(&Fb, I, ctx))
            {
                polyset_append(&Fb, I, ctx);
                wu_solve_rec(F_orig, &Fb, out, depth + 1, vars, ctx);
            }
            polyset_clear(&Fb, ctx);
        }
        nmod_mpoly_clear(I, ctx);
    }

    polyset_clear(&CS, ctx);
}

/* ------------------------------------------------------------------ */
/* 主程序：示例                                                        */
/* ------------------------------------------------------------------ */

int main(void)
{
    /* 变元顺序即消元顺序：x < y < z */
    const char *vars[] = { "x", "y", "z" };
    slong nvars = 3;
    ulong p = 13;               /* 素数域 F_13，可改 */

    /* 待解系统 F ⊂ F_p[x,y,z]，字符串按需修改即可 */
    /* e1=5, e2=8, e3=4  =>  x,y,z 是 t^3-5t^2+8t-4=(t-1)(t-2)^2 的根，
       解应为 (1,2,2) 的全部排列，共 3 组 */
    const char *system_strs[] = {
        "x^10 + y^10 + z^10 - 5",
        "x*y + y*z + z*x - 8",
        "x*y*z - 4",
    };
    slong nf = sizeof(system_strs) / sizeof(system_strs[0]);

    nmod_mpoly_ctx_t ctx;
    polyset_t F;
    sol_list_t sols;
    slong i;

    nmod_mpoly_ctx_init(ctx, nvars, ORD_LEX, p);
    polyset_init(&F);
    sol_list_init(&sols, nvars);

    printf("======  吴特征列方法 / F_%lu  ======\n", (unsigned long) p);
    printf("变元序: ");
    for (i = 0; i < nvars; i++)
        printf("%s%s", vars[i], i + 1 < nvars ? " < " : "\n");

    for (i = 0; i < nf; i++)
    {
        nmod_mpoly_t f;
        nmod_mpoly_init(f, ctx);
        if (nmod_mpoly_set_str_pretty(f, system_strs[i], vars, ctx) != 0)
        {
            fprintf(stderr, "解析失败: %s\n", system_strs[i]);
            nmod_mpoly_clear(f, ctx);
            continue;
        }
        polyset_append(&F, f, ctx);
        nmod_mpoly_clear(f, ctx);
    }
    print_polyset("输入系统 F:", &F, vars, ctx);

    wu_solve_rec(&F, &F, &sols, 0, vars, ctx);

    printf("\nF_%lu 上的解 (共 %ld 组):\n",
           (unsigned long) p, (long) sols.count);
    for (i = 0; i < sols.count; i++)
    {
        slong v;
        printf("  (");
        for (v = 0; v < nvars; v++)
            printf("%s=%lu%s", vars[v],
                   (unsigned long) sols.vals[i * nvars + v],
                   v + 1 < nvars ? ", " : "");
        printf(")\n");
    }

    sol_list_clear(&sols);
    polyset_clear(&F, ctx);
    nmod_mpoly_ctx_clear(ctx);
    return 0;
}
