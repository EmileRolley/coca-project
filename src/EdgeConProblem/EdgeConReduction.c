#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "EdgeConReduction.h"
#include "Z3Tools.h"

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
static Z3_ast build_phi_5(g_context_s *ctx);
static Z3_ast build_phi_8(g_context_s *ctx);
static g_context_s* init_g_context(Z3_context z3_ctx, EdgeConGraph graph, int cost);

Z3_ast getVariableIsIthTranslator(Z3_context ctx, int node1, int node2, int number) {
    char name[40];

    if (node1 < node2) {
        snprintf(name, 40, "[(%d,%d),%d]", node1, node2, number);
    }
    else {
        snprintf(name, 40, "[(%d,%d),%d]", node2, node1, number);
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

Z3_ast EdgeConReduction(Z3_context ctx, EdgeConGraph edgeGraph, int cost) {
    g_context_s *gctx;

    gctx = init_g_context(ctx, edgeGraph, cost);

    return Z3_mk_and(ctx, 5, (Z3_ast [5]) {
            build_phi_2(gctx),
            build_phi_3(gctx),
            build_phi_4(gctx),
            build_phi_5(gctx),
            build_phi_8(gctx)
        }
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

static Z3_ast build_phi_5(g_context_s *ctx) {
    int pos;
    Z3_ast literals[ctx->C_H * (ctx->N - ctx->k)];

    pos = 0;
    for (int i = 0; i < ctx->C_H; ++i) {
        for (int n = ctx->k; n < ctx->N; ++n) {
            literals[pos++] = getVariableLevelInSpanningTree(ctx->z3_ctx, n, i);
        }
    }

    return Z3_mk_or(ctx->z3_ctx, pos, literals);
}

static Z3_ast build_phi_8(g_context_s *ctx) { return Z3_mk_false(ctx->z3_ctx); }

void getTranslatorSetFromModel(Z3_context ctx, Z3_model model, EdgeConGraph graph) {
    return;
}