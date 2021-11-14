#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "EdgeConReduction.h"
#include "Z3Tools.h"

/** Macros used to improve the readability of formula construction. */

#define NOT(X) Z3_mk_not(ctx->z3_ctx, X)
#define AND(n) Z3_mk_and(ctx->z3_ctx, n, (Z3_ast[n]) {
#define EAND })
#define OR(n) Z3_mk_or(ctx->z3_ctx, n, (Z3_ast[n]) {
#define EOR })

#define X_(n1, n2, i) getVariableIsIthTranslator(ctx->z3_ctx, n1, n2, i)
#define P_(j1, j2) getVariableParent(ctx->z3_ctx, j1, j2)
#define L_(j, h) getVariableLevelInSpanningTree(ctx->z3_ctx, h, j)

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

static Z3_ast build_phi_2(g_context_s *ctx);
static Z3_ast build_phi_3(g_context_s *ctx);
static Z3_ast build_phi_4(g_context_s *ctx);
static Z3_ast build_phi_8(g_context_s *ctx);

/**
 * Builds the formula ensuring the constraint:
 *
 *  "The tree has a depth strictly greater than k"
 *
 * @param ctx is the current reduction context.
 *
 * @return the Z3 ast corresponding to the formula.
 */
static Z3_ast build_phi_5(const g_context_s *ctx);
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
        OR(5)
            build_phi_2(ctx),
            build_phi_3(ctx),
            build_phi_4(ctx),
            build_phi_5(ctx),
            build_phi_8(ctx)
        EOR
    );
}

static g_context_s* init_g_context(Z3_context z3_ctx, EdgeConGraph graph, int cost) {
    g_context_s *ctx = NULL;

    ctx = malloc(sizeof(g_context_s));
    assert( NULL != ctx );

    ctx->graph = graph;
    ctx->G = getGraph(graph);
    ctx->n = ctx->G.numNodes;
    ctx->m = ctx->G.numEdges;
    ctx->C_H = getNumComponents(graph);
    ctx->N = ctx->C_H - 1;
    ctx->k = cost;
    ctx->z3_ctx = z3_ctx;

    return ctx;
}

static Z3_ast build_phi_2(g_context_s *ctx) { return Z3_mk_false(ctx->z3_ctx); }
static Z3_ast build_phi_3(g_context_s *ctx) { return Z3_mk_false(ctx->z3_ctx); }
static Z3_ast build_phi_4(g_context_s *ctx) { return Z3_mk_false(ctx->z3_ctx); }

/** FIXME: needs to manage the case k > N. */
static Z3_ast build_phi_5(const g_context_s *ctx) {
    int pos;
    Z3_ast literals[ctx->C_H * (ctx->N - ctx->k)];

    pos = 0;
    for (int i = 0; i < ctx->C_H; ++i) {
        for (int n = ctx->k; n < ctx->N; ++n) {
            literals[pos++] = L_(n, i);
        }
    }

    return Z3_mk_or(ctx->z3_ctx, pos, literals);
}

static Z3_ast build_phi_8(g_context_s *ctx) { return Z3_mk_false(ctx->z3_ctx); }

void getTranslatorSetFromModel(Z3_context ctx, Z3_model model, EdgeConGraph graph) {
    int m;
    int N;

    m = getGraph(graph).numEdges;
    computesHomogeneousComponents(graph);
    N = getNumComponents(graph) - 1;

    for (int n1 = 0; n1 < m; ++n1) {
        for (int n2 = n1; n2 < m; ++n2) {
            for (int i = 0; i < N; ++i) {
                if (is_the_ith_translator(ctx, model, graph, n1, n2, i)) {
                    addTranslator(graph, n1, n2);
                }
            }
        }
    }
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
        && isEdgeHeterogeneous(graph, n1, n2)
    );
}
