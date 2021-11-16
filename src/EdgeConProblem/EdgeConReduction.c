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

static Z3_ast build_phi_2(const g_context_s *ctx);
static Z3_ast build_phi_3(const g_context_s *ctx);
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


static Z3_ast build_phi_2(const g_context_s *ctx){
    int tab1Size = (ctx->m * (ctx->m - 1)) / 2;     // /!\ A REVOIR
    Z3_ast resTab1[tab1Size];
    int tabId = 0;

    for (int i = 0; i < ctx->N; i++){
        for(int e1 = 0; e1 < ctx->m; e1++){             // 1st node of e
            for(int e2 = e1 + 1; e2 < ctx->m; e2++){    // 2nd node of e
                for(int j1 = 0; j1 > e1 && j1 < ctx->m; j1++){  // 1st node of j  
                    for (int j2 = j1 + 1; j2 < ctx->m; j2++){   // 2nd node of j
                        // j1 > e1 : car on ne test qu'une fois une paire d'arêtes
                        if(isEdge(ctx->G, e1, e2) && isEdge(ctx->G, j1, j2)){
                            Z3_ast e_i = X_(e1, e2, i);
                            Z3_ast j_i = X_(j1, j2, i);
                            Z3_ast not_e_i = NOT(e_i);
                            Z3_ast not_j_i = NOT(j_i);
                            resTab1[tabId++] =  OR(2) 
                                                    not_e_i,
                                                    not_j_i
                                                EOR;
                        }
                    }
                }
            }
        }
    }

    Z3_ast res1 = Z3_mk_and(ctx->z3_ctx, tabId, (Z3_ast *) resTab1);

    int tab2Size = ((ctx->m) * (((ctx->N) * (ctx->N)) / 2));
    Z3_ast resTab2[tab2Size];
    tabId = 0;

    for(int e1 = 0; e1 < ctx->m; e1++){
        for(int e2 = e1 + 1; e2 < ctx->m; e2++){
            if(isEdge(ctx->G, e1, e2)){
                for(int i = 0; i < ctx->N; i++){
                    for(int j = i + 1; j < ctx->N; j++){
                        Z3_ast e_i = X_(e1, e2, i);
                        Z3_ast e_j = X_(e1, e2, j);
                        Z3_ast not_e_i = NOT(e_i);
                        Z3_ast not_e_j = NOT(e_j);
                        resTab2[tabId++] =  OR(2) 
                                                not_e_i,
                                                not_e_j
                                            EOR;
                    }
                }
            } 
        }
    }

    Z3_ast res2 = Z3_mk_and(ctx->z3_ctx, tabId, (Z3_ast *) resTab2);
    Z3_ast res[2] = {res1, res2}; 
    return Z3_mk_and(ctx->z3_ctx, 2, res);
}

static Z3_ast build_phi_3(const g_context_s *ctx) { 
    
    int tab1Size = (ctx->C_H - 1) * (ctx->C_H - 1);
    Z3_ast resTab1[tab1Size];
    int tabId = 0;

    for(int j = 2; j < ctx->C_H; j++){
        for(int j_prime = j + 1; j_prime < ctx->N; j_prime ++){
            resTab1[tabId++] = P_(j, j_prime);
        }
    }

    Z3_ast res1 = Z3_mk_and(ctx->z3_ctx, tabId, (Z3_ast *) resTab1);
    
    int tab2Size = ((ctx->C_H - 1) * (ctx->C_H - 1) * (ctx->C_H - 1)) * 2;
    Z3_ast resTab2[tab2Size];
    tabId = 0;

    for(int j = 2; j < ctx->C_H; j++){
        for(int j_prime = j + 1; j_prime < ctx->C_H; j_prime++){
            for(int j_prime2 = j_prime + 1; j_prime2 < ctx->C_H; j_prime2++){
                Z3_ast p_j_jprime = P_(j, j_prime);
                Z3_ast p_j_jprime2 = P_(j, j_prime2);
                Z3_ast not_p_j_jprime = NOT(p_j_jprime);
                Z3_ast not_p_j_jprime2 = NOT(p_j_jprime2);
                resTab2[tabId++] =  OR(2) 
                                        not_p_j_jprime,
                                        not_p_j_jprime2
                                    EOR;
            }
        }
    }
    
    Z3_ast res2 = Z3_mk_and(ctx->z3_ctx, tabId, (Z3_ast *) resTab2);
    Z3_ast res[2] = {res1, res2}; 
    return Z3_mk_and(ctx->z3_ctx, 2, res);
}


static Z3_ast build_phi_4(const g_context_s *ctx){
    int tab1Size = ctx->C_H * (ctx->N);
    Z3_ast resTab1[tab1Size];
    int tabId = 0;

    for(int i = 1; i < ctx->C_H; i++){
        for(int n = 1; i < ctx->N; n++){
            resTab1[tabId++] = L_(i, n);
        }
    }

    Z3_ast res1 = Z3_mk_and(ctx->z3_ctx, tabId, (Z3_ast *) resTab1);

    int tab2Size = ctx->C_H * ((ctx->N * ctx->N) / 2) * 2;
    Z3_ast resTab2[tab2Size];
    tabId = 0;

    for(int i = 1; i < ctx->C_H; i++){
        for(int n = 1; n < ctx->N; n++){
            for(int n_prime = n + 1; n_prime < ctx->N; n_prime++){
                Z3_ast l_i_n = L_(i, n);
                Z3_ast l_i_nprime = L_(i, n_prime);
                Z3_ast not_l_i_n = NOT(l_i_n);
                Z3_ast not_l_i_nprime = NOT(l_i_nprime);
                resTab2[tabId++] =  AND(2) 
                                        not_l_i_n,
                                        not_l_i_nprime
                                    EAND;
            }  
        }
    }

    Z3_ast res2 = Z3_mk_and(ctx->z3_ctx, tabId, (Z3_ast *) resTab2);
    Z3_ast res[2] = {res1, res2}; 
    return Z3_mk_and(ctx->z3_ctx, 2, res);
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