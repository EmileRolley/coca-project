#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "EdgeConReduction.h"
#include "Z3Tools.h"

#define MAX(X, Y) X > Y ? X : Y

/** Macros used to improve the readability of formula construction. */

#define NOT(X) Z3_mk_not(ctx->z3_ctx, X)
#define AND(n) Z3_mk_and(ctx->z3_ctx, n, (Z3_ast[n]) {
#define EAND })
#define OR(n) Z3_mk_or(ctx->z3_ctx, n, (Z3_ast[n]) {
#define EOR })

#define X_(n1, n2, i) getVariableIsIthTranslator(ctx->z3_ctx, n1, n2, i)
#define P_(j1, j2) getVariableParent(ctx->z3_ctx, j1, j2)
#define L_(j, h) getVariableLevelInSpanningTree(ctx->z3_ctx, h, j)

#define FORALL_TRANSLATOR(I) \
    for (int I = 0; I < ctx->N; I++) {

#define EFI }

#define FORALL_EDGE(N1, N2) \
        for (int N1 = 0; N1 < ctx->n; ++N1) { \
            for (int N2 = N1 + 1; N2 < ctx->n; ++N2) { \
                if (isEdge(ctx->G, N1, N2)) {

#define EFE }}}

#define FORALL_COMPONENT(J) \
    for (int J = 0; J < ctx->C_H; J++) {

#define FORALL_COMPONENT_EXCEPT_ROOT(J) \
    for (int J = 1; J < ctx->C_H; J++) {

#define EFC }

#define FORALL_LEVEL(n) \
    for (int n = 0; n < ctx->N; n++) {

#define EFL }


/** Stores all needed data used to build formulas. */
typedef struct {
    unsigned int n;     ///< The numbers of vertex.
    unsigned int m;     ///< The number of edges.
    unsigned int N;     ///< The minimal number of translator.
    int C_H;            ///< The number of homogeneous components.
    int k;              ///< The maximum cost of a simple and valid path between two vertex.
    Graph G;            ///< The graph.
    EdgeConGraph graph; ///< The EdgeConGraph.
    Z3_context z3_ctx;  ///< The current Z3 context.
} g_context_s;


/**
 * Builds the formula ensuring the constraint:
 *
 *   "Each translator can only be associated with at most one edge"
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_2_1(const g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "Each edge can only receive at most one translator"
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_2_2(const g_context_s *ctx);

/**
 * Builds the conjunction of the formulas phi_2_1 and phi_2_2
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_2(const g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "Each homogeneous components own at least one parent, except the root"
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_3_1(const g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "Each homogeneous components own at most one parent, except the root"
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_3_2(const g_context_s *ctx);

/**
 * Builds the conjunction of the formulas phi_3_1 and phi_3_2
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_3(const g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "Each homogeneous components own at least one level"
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_4_1(const g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "Each homogeneous components own at most one level"
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_4_2(const g_context_s *ctx);

/**
 * Builds the conjunction of the formulas phi_4_1 and phi_4_2
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_4(const g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "The tree has a depth strictly greater than k."
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_5(const g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "For two homogeneous components, exists an edge (u, v) between X_@p j1 and
 *    X_@p j2 and one of them have a translator."
 *
 * @param ctx is the current reduction context.
 * @param j1 is the number of the first homogeneous component.
 * @param j2 is the number of the second homogeneous component.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_6(const g_context_s *ctx, const int j1, const int j2);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "For two homogeneous components, if X_@p j1 is at level h then X_@p j2
 *    is at level h - 1."
 *
 * @param ctx is the current reduction context.
 * @param j1 is the number of the first homogeneous component.
 * @param j2 is the number of the second homogeneous component.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_7(const g_context_s *ctx, const int j1, const int j2);

/**
 * Builds the formula ensuring the constraint:
 *
 *   "For any two homogeneous components, if X_j1 is a parent of X_j2, then the
 *    conditions of phi_6 and phi_7 are satisfied."
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_8(const g_context_s *ctx);

static g_context_s* init_g_context(Z3_context z3_ctx, EdgeConGraph graph, int cost);

/**
 * Checks if the edge (@p n1, @p n2) is the @p i -th translator.
 *
 * @param ctx is the solver context.
 * @param model is the solver model.
 * @param graph is a EdgeConGraph.
 * @param n1 is the first node of the edge.
 * @param n2 is the second node of the edge.
 * @param i is number of the the translator.
 *
 * @return true if the edge (@p n1, @p n2) is the @p i -th translator of @p
 * graph, otherwise false.
 */
static bool is_the_ith_translator(
    const Z3_context ctx,
    const Z3_model model,
    const EdgeConGraph graph,
    const int n1,
    const int n2,
    const int i
);

Z3_ast getVariableIsIthTranslator(Z3_context ctx, int node1, int node2, int number) {
    char name[40];

    if (node1 < node2) {
        snprintf(name, 40, "x_[(%d,%d),%d]", node1, node2, number);
    }
    else {
        snprintf(name, 40, "x_[(%d,%d),%d]", node2, node1, number);
    }

    return mk_bool_var(ctx, name);
}

Z3_ast getVariableParent(Z3_context ctx, int child, int parent) {
    char name[40];

    snprintf(name, 40, "p_[%d,%d]", child, parent);

    return mk_bool_var(ctx, name);
}

Z3_ast getVariableLevelInSpanningTree(Z3_context ctx, int level, int component) {
    char name[40];

    snprintf(name, 40, "l_[%d,%d]", component, level);

    return mk_bool_var(ctx, name);
}

Z3_ast EdgeConReduction(Z3_context z3_ctx, EdgeConGraph edgeGraph, int cost) {
    g_context_s *ctx;

    ctx = init_g_context(z3_ctx, edgeGraph, cost);

    return(
        AND(5)
            build_phi_2(ctx),
            build_phi_3(ctx),
            build_phi_4(ctx),
            build_phi_5(ctx),
            build_phi_8(ctx)
        EAND
    );
}

static g_context_s *init_g_context(Z3_context z3_ctx, EdgeConGraph graph, int cost) {
    g_context_s *ctx = NULL;

    ctx = malloc(sizeof(g_context_s));
    assert( NULL != ctx );

    ctx->graph = graph;
    ctx->G = getGraph(graph);
    ctx->n = orderG(ctx->G);
    ctx->m = sizeG(ctx->G);
    ctx->C_H = getNumComponents(graph);
    ctx->N = ctx->C_H - 1;
    ctx->k = cost;
    ctx->z3_ctx = z3_ctx;

    return ctx;
}


static Z3_ast build_phi_2(const g_context_s *ctx) {
    return (
        AND(2)
            build_phi_2_1(ctx),
            build_phi_2_2(ctx)
        EAND
    );
}
static Z3_ast build_phi_2_1(const g_context_s *ctx) {
    int pos;
    Z3_ast phi_2_1[ctx->N * (ctx->m * ctx->m - 1)];

    pos = 0;
    FORALL_TRANSLATOR(i)
        FORALL_EDGE(e1, e2)
            FORALL_EDGE(f1, f2)
                if (e1 != f1 || e2 != f2) {
                    phi_2_1[pos++] =
                        OR(2)
                            NOT( X_(e1, e2, i) ),
                            NOT( X_(f1, f2, i) )
                        EOR;
                }
            EFE
        EFE
    EFI

    return Z3_mk_and(ctx->z3_ctx, pos, phi_2_1);
}

static Z3_ast build_phi_2_2(const g_context_s *ctx) {
    int pos;
    Z3_ast phi_2_2[ (ctx->m * ((ctx->N * ctx->N) / 2)) ];

    if (1 == ctx->N) {
        return Z3_mk_true(ctx->z3_ctx);
    }

    pos = 0;
    FORALL_EDGE(e1, e2)
        FORALL_TRANSLATOR(i)
            for (int j = i + 1; j < ctx->N; j++) {
                phi_2_2[pos++] =
                    OR(2)
                        NOT( X_(e1, e2, i) ),
                        NOT( X_(e1, e2, j) )
                    EOR;
            }
        EFI
    EFE

    return Z3_mk_and(ctx->z3_ctx, pos, phi_2_2);
}

static Z3_ast build_phi_3(const g_context_s *ctx) {
    return (
        AND(2)
            build_phi_3_1(ctx),
            build_phi_3_2(ctx)
        EAND
    );
}

static Z3_ast build_phi_3_1(const g_context_s *ctx) {
    int pos, pos2;
    Z3_ast phi_3_1[ctx->C_H];

    pos = 0;
    FORALL_COMPONENT_EXCEPT_ROOT(j1)
        Z3_ast phi_3_1_disj[ctx->C_H];

        pos2 = 0;
        FORALL_COMPONENT(j2)
            if (j1 != j2) {
                phi_3_1_disj[pos2++] = P_(j1, j2);
            }
        EFC
        phi_3_1[pos++] = Z3_mk_or(ctx->z3_ctx, pos2, phi_3_1_disj);
    EFC

    return Z3_mk_and(ctx->z3_ctx, pos, phi_3_1);
}

static Z3_ast build_phi_3_2(const g_context_s *ctx) {
    int pos;
    Z3_ast phi_3_2[ (ctx->C_H - 1) * (ctx->C_H - 1) * (ctx->C_H - 1) ];

    pos = 0;
    FORALL_COMPONENT_EXCEPT_ROOT(j)
        FORALL_COMPONENT(j1)
            if (j1 != j) {
                for (int j2 = j1 + 1; j2 < ctx->C_H; j2++) {
                    if (j2 != j) {
                        phi_3_2[pos++] =
                            OR(2)
                                NOT( P_(j, j1) ),
                                NOT( P_(j, j2) )
                            EOR;
                    }
                }
            }
        EFC
    EFC

    return Z3_mk_and(ctx->z3_ctx, pos, phi_3_2);
}

static Z3_ast build_phi_4(const g_context_s *ctx){
    return (
        AND(2)
            build_phi_4_1(ctx),
            build_phi_4_2(ctx)
        EAND
    );
}

static Z3_ast build_phi_4_1(const g_context_s *ctx) {
    int pos, pos2;
    Z3_ast phi_4_1[ctx->C_H];

    pos = 0;
    FORALL_COMPONENT(i)
        Z3_ast phi_4_1_disj[ctx->N];

        pos2 = 0;
        FORALL_LEVEL(n)
            phi_4_1_disj[pos2++] = L_(i, n);
        EFL
        phi_4_1[pos++] = Z3_mk_or(ctx->z3_ctx, pos2, phi_4_1_disj);
    EFC

    return Z3_mk_and(ctx->z3_ctx, pos, phi_4_1);
}

static Z3_ast build_phi_4_2(const g_context_s *ctx) {
    int pos;
    Z3_ast phi_4_2[ ctx->C_H * (ctx->N * ctx->N) ];

    pos = 0;
    FORALL_COMPONENT(i)
        FORALL_LEVEL(n1)
            for (int n2 = n1 + 1; n2 < ctx->N; ++n2) {
                phi_4_2[pos++] =
                    OR(2)
                        NOT( L_(i, n1) ),
                        NOT( L_(i, n2) )
                    EOR;
            }
        EFL
    EFC

    return Z3_mk_and(ctx->z3_ctx, pos, phi_4_2);
}

static Z3_ast build_phi_5(const g_context_s *ctx) {
    int pos;
    Z3_ast phi_5[
        ctx->C_H *
        (ctx->N <= ctx->k ? ctx->N : (ctx->N - ctx->k))
    ];

    pos = 0;
    FORALL_COMPONENT(i)
        for (int n = ctx->k; n < ctx->N; ++n) {
            phi_5[pos++] = L_(i, n);
        }
    EFC

    return Z3_mk_or(ctx->z3_ctx, pos, phi_5);
}

static Z3_ast build_phi_8(const g_context_s *ctx) {
    int pos;
    Z3_ast phi_8[ctx->C_H * ctx->C_H];

    pos = 0;
    FORALL_COMPONENT(j1)
        FORALL_COMPONENT(j2)
            if (j1 != j2) {
                phi_8[pos++] =
                    AND(2)
                        OR(2)
                            NOT( P_(j1, j2) ),
                            build_phi_6(ctx, j1, j2)
                        EOR,
                        OR(2)
                            NOT( P_(j1, j2) ),
                            build_phi_7(ctx, j1, j2)
                        EOR
                    EAND;
            }
        EFC
    EFC

    return Z3_mk_and(ctx->z3_ctx, pos, phi_8);
}

static Z3_ast build_phi_6(const g_context_s *ctx, const int j1, const int j2) {
    int pos;
    Z3_ast phi_6[ctx->m * ctx->N];

    pos = 0;
    FORALL_EDGE(u, v)
        if (isNodeInComponent(ctx->graph, v, j1) &&
            isNodeInComponent(ctx->graph, u, j2))
        {
            FORALL_LEVEL(i)
                phi_6[pos++] = X_(u, v, i);
            EFL
        }
    EFE

    if (0 == pos) {
        return Z3_mk_false(ctx->z3_ctx);
    }

    return Z3_mk_or(ctx->z3_ctx, pos, phi_6);
}

static Z3_ast build_phi_7(const g_context_s *ctx, const int j1, const int j2) {
    int pos;
    Z3_ast phi_7[ctx->N];

    pos = 0;
    for (int h = 1; h < ctx->N; ++h) {
        phi_7[pos++] =
            OR(2)
                NOT( L_(j1, h) ),
                L_(j2, h - 1)
            EOR;
    }

    return Z3_mk_and(ctx->z3_ctx, pos, phi_7);
}

void getTranslatorSetFromModel(Z3_context ctx, Z3_model model, EdgeConGraph graph) {
    int n;
    int N;

    n = orderG(getGraph(graph));
    N = getNumComponents(graph) - 1;

    for (int n1 = 0; n1 < n; ++n1) {
        for (int n2 = n1 + 1; n2 < n; ++n2) {
            if (isEdge(getGraph(graph), n1, n2)) {
                for (int i = 0; i < N; ++i) {
                    if (is_the_ith_translator(ctx, model, graph, n1, n2, i)) {
                        addTranslator(graph, n1, n2);
                    }
                }
            }
        }
    }
    computesHomogeneousComponents(graph);
}

static bool is_the_ith_translator(
    const Z3_context ctx,
    const Z3_model model,
    const EdgeConGraph graph,
    const int n1,
    const int n2,
    const int i
) {
    return(
        valueOfVarInModel(ctx, model, getVariableIsIthTranslator(ctx, n1, n2, i))
    );
}
