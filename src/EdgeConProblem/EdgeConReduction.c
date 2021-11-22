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
static Z3_ast build_phi_2_1(const g_context_s *ctx);

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
 * FIXME: needs to manage the case k > N.
 *
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
 * FIXME: is the DM2 report h start at 1 but it should start at 2 because of the h-1.
 *
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

static Z3_ast build_phi_2_1(const g_context_s *ctx){
    int nbVariables = (ctx->m * (ctx->m - 1)) / 2;
    Z3_ast formula[nbVariables];
    int formulaId = 0;

    for (int i = 0; i < ctx->N; i++){
        for(int e1 = 0; e1 < ctx->m; e1++){             // 1st node of e
            for(int e2 = e1 + 1; e2 < ctx->m; e2++){    // 2nd node of e
                for(int f1 = 0; f1 < ctx->m; f1++){     // 1st node of f  
                    for (int f2 = f1 + 1; f2 < ctx->m; f2++){   // 2nd node of f
                        if((e1 != f1 || e2 != f2) && isEdge(ctx->G, e1, e2) && isEdge(ctx->G, f1, f2)){
                            formula[formulaId++] =  
                                OR(2) 
                                    NOT( X_(e1, e2, i)),
                                    NOT( X_(f1, f2, i))
                                EOR;
                        }
                    }
                }
            }
        }
    }

    return Z3_mk_and(ctx->z3_ctx, formulaId, (Z3_ast *) formula);
}


static Z3_ast build_phi_2_2(const g_context_s *ctx){
    int nbVariables = ((ctx->m) * (((ctx->N) * (ctx->N)) / 2));
    Z3_ast formula[nbVariables];
    int formulaId = 0;

    for(int e1 = 0; e1 < ctx->m; e1++){
        for(int e2 = e1 + 1; e2 < ctx->m; e2++){
            if(isEdge(ctx->G, e1, e2)){
                for(int i = 0; i < ctx->N; i++){
                    for(int f = i + 1; f < ctx->N; f++){
                        formula[formulaId++] =  
                            OR(2) 
                                NOT( X_(e1, e2, i) ),
                                NOT( X_(e1, e2, f) )
                            EOR;
                    }
                }
            } 
        }
    }

    return Z3_mk_and(ctx->z3_ctx, formulaId, (Z3_ast *) formula);
}


static Z3_ast build_phi_2(const g_context_s *ctx){
    return (
        AND(2)
            build_phi_2_1(ctx),
            build_phi_2_2(ctx)
        EAND
    );
}

static Z3_ast build_phi_3_1(const g_context_s *ctx){
    Z3_ast formula[ctx->C_H];
    int formulaId = 0;

    for(int j = 1; j < ctx->C_H; j++){
        Z3_ast disjunctionTab[ctx->C_H];
        int disjunctionformulaId = 0;
        for(int j_prime = 0; j_prime < ctx->N; j_prime ++){
            if( j != j_prime){
                disjunctionTab[disjunctionformulaId] = P_(j, j_prime);
            }
        }
        formula[formulaId++] = Z3_mk_or(ctx->z3_ctx, disjunctionformulaId, (Z3_ast *) disjunctionTab);
    }

    return Z3_mk_and(ctx->z3_ctx, formulaId, (Z3_ast *) formula);
}

static Z3_ast build_phi_3_2(const g_context_s *ctx) { 
    int nbVariables = ((ctx->C_H - 1) * (ctx->C_H - 1) * (ctx->C_H - 1)) * 2;
    Z3_ast forlumaTab[nbVariables];
    int formulaId = 0;

    for(int j = 0; j < ctx->C_H; j++){
        for(int j_prime = j + 1; j_prime < ctx->C_H; j_prime++){
            for(int j_prime2 = j_prime + 1; j_prime2 < ctx->C_H; j_prime2++){
                forlumaTab[formulaId++] =  
                    OR(2) 
                        NOT( P_(j, j_prime) ),
                        NOT( P_(j, j_prime2) )
                    EOR;
            }
        }
    }

    return Z3_mk_and(ctx->z3_ctx, formulaId, (Z3_ast *) forlumaTab);
}

static Z3_ast build_phi_3(const g_context_s *ctx) { 
    return (
        AND(2)
            build_phi_3_1(ctx),
            build_phi_3_2(ctx)
        EAND
    );
}

static Z3_ast build_phi_4_1(const g_context_s *ctx){
    Z3_ast formula[ctx->C_H];
    int formulaId = 0;

    for(int i = 0; i < ctx->C_H; i++){
        Z3_ast disjunctionTab[ctx->N];
        int disjunctionformulaId = 0
        for(int n = 0; i < ctx->N; n++){
            disjunctionTab[disjunctionformulaId] = L_(i, n);
        }
        formula[formulaId++] = Z3_mk_or(ctx->z3_ctx, disjunctionformulaId, (Z3_ast *) disjunctionTab);
    }

    return Z3_mk_and(ctx->z3_ctx, formulaId, (Z3_ast *) formula);
}

static Z3_ast build_phi_4_2(const g_context_s *ctx){
    int nbVariables = ctx->C_H * ((ctx->N * ctx->N) / 2) * 2;
    Z3_ast formula[nbVariables];
    formulaId = 0;

    for(int i = 0; i < ctx->C_H; i++){
        for(int n = 0; n < ctx->N; n++){
            for(int n_prime = n + 1; n_prime < ctx->N; n_prime++){
                formula[formulaId++] =  
                    OR(2) 
                        NOT( L_(i, n) ),
                        NOT( L_(i, n_prime) )
                    EOR;
            }  
        }
    }

    return Z3_mk_and(ctx->z3_ctx, formulaId, (Z3_ast *) formula);
}

static Z3_ast build_phi_4(const g_context_s *ctx){
    return (
        AND(2)
            build_phi_4_1(ctx),
            build_phi_4_2(ctx)
        EAND
    );
}




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

static Z3_ast build_phi_6(const g_context_s *ctx, const int j1, const int j2) {
    int pos;
    Z3_ast literals[ctx->m * ctx->N];

    pos = 0;
    for (int u = 0; u < ctx->m; ++u) {
        for (int v = u + 1; v < ctx->m; ++v) {
            if (isEdge(ctx->G, u, v) &&
                isNodeInComponent(ctx->graph, u, j1) &&
                isNodeInComponent(ctx->graph, v, j2)) {
                for (int i = 0; i < ctx->N; ++i) {
                    literals[pos++] = X_(u, v, i);
                }
            }
        }
    }

    return Z3_mk_or(ctx->z3_ctx, pos, literals);
}

static Z3_ast build_phi_7(const g_context_s *ctx, const int j1, const int j2) {
    int pos;
    Z3_ast literals[ctx->N];

    pos = 0;
    for (int h = 1; h < ctx->N; ++h) {
        literals[pos++] =
            OR(2)
                NOT( L_(j1, h) ),
                L_(j2, h - 1)
            EOR;
    }

    return Z3_mk_or(ctx->z3_ctx, pos, (Z3_ast *) literals);
}


static Z3_ast build_phi_8(const g_context_s *ctx) {
    int pos;
    Z3_ast literals[ctx->C_H * ctx->C_H];

    pos = 0;
    for (int j1 = 0; j1 < ctx->C_H - 1; ++j1) {
        for (int j2 = j1 + 1; j2 < ctx->C_H; ++j2) {
            Z3_ast not_p_j1_j2;

            not_p_j1_j2 = NOT( P_(j1, j2) );
            literals[pos++] =
                AND(2)
                    OR(2)
                        not_p_j1_j2,
                        build_phi_6(ctx, j1, j2),
                    EOR,
                    OR(2)
                        not_p_j1_j2,
                        build_phi_7(ctx, j1, j2)
                    EOR
                EAND;
        }
    }

    return Z3_mk_and(ctx->z3_ctx, pos, literals);
}

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