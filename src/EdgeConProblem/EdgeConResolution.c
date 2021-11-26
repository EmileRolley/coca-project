#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "EdgeConResolution.h"
#include "Graph.h"
#include "BruteForceUtils.h"

int MaxCost(Graph graph, bool *C);
int MaxCostAux(Graph graph, bool *C, int n, int *col);

int BruteForceEdgeCon(EdgeConGraph graph) {
    Graph g = getGraph(graph);
    int numHeteregeneousEdges = getNumHeteregeneousEdges(graph);
    int heterogeneousEdges[numHeteregeneousEdges];
    int N;
    int cost;
    int n = orderG(g);
    int maxSubHt;
    int numSubHt;
    bool subSetOfHt[n * n];
    bool valid;

    N = getNumComponents(graph) - 1;
    maxSubHt = binCoeff(numHeteregeneousEdges, N);

    if (0 == maxSubHt) {
        return -1;
    }

    getHeterogeneousEdges(graph, heterogeneousEdges);

    for (int k = 1; k <= N; k++) {
        valid = true;
        numSubHt = 0;
        while (valid && numSubHt < maxSubHt) {

            memset(subSetOfHt, 0, sizeof(bool) * n * n);

            getSubSetOfHeterogeneousEdges(
                heterogeneousEdges,
                numHeteregeneousEdges,
                N,
                numSubHt,
                subSetOfHt
            );

            cost = MaxCost(g, subSetOfHt);
            if (cost > 0 && cost > k) {
                valid = false;
            }
            ++numSubHt;
        }
        if (valid) {
            updateGraphTranslators(graph, subSetOfHt);
            computesHomogeneousComponents(graph);
            return k;
        }
    }

    updateGraphTranslators(graph, subSetOfHt);
    computesHomogeneousComponents(graph);
    return N;
}

#define WHITE 0
#define GREY  1
#define BLACK 2

int MaxCost(Graph graph, bool *C) {
    int max = 0;
    int n = orderG(graph);
    int maxPrime;
    int col[orderG(graph)];

    for (int node = 0; node < n; node++) {
        maxPrime = MaxCostAux(graph, C, node, col);

        for (int i = 0; i < n; i++) {
            if (col[i] == WHITE) {
                return 0;
            }
        }

        if (maxPrime > max) {
            max = maxPrime;
        }
    }
    return max;
}

int MaxCostAux(Graph graph, bool *C, int s, int *col) {
    int n = orderG(graph);
    int queueNodesMaxSize = n;
    int queueNodes[queueNodesMaxSize];
    int queueNodesRear = -1;
    int queueNodesFront = -1;
    int cost[ n ];

    memset(col, WHITE, sizeof(int) * n);
    memset(cost, WHITE, sizeof(int) * n);

    col[s] = GREY;
    queueAdd(s, queueNodes, &queueNodesRear, &queueNodesFront, queueNodesMaxSize);

    int x;
    while (queueNodesRear >= queueNodesFront) {
        x = queuePop(queueNodes, &queueNodesRear, &queueNodesFront);
        if (x == -1) {
            return -1;
        }

        for (int y = 0; y < n; y++) {
            if (isEdge(graph, x, y)) {
                if (col[y] == WHITE) {
                    cost[y] = cost[x];

                    /* If (x, y) includes in C */
                    if ((x < y && C[x * n + y]) || C[y * n + x]) {
                        ++cost[y];
                    }

                    col[y] = GREY;
                    queueAdd(y, queueNodes, &queueNodesRear, &queueNodesFront, queueNodesMaxSize);
                }
            }
        }
        col[x] = BLACK;
    }
    return maxOfArray(cost, n);
}
