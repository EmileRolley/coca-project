#include "EdgeConResolution.h"
#include "Graph.h"
#include "BruteForceUtils.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

const int WHITE = 0;
const int GREY = 1;
const int BLACK = 2;

int MaxCost(Graph graph, bool *C);
int MaxCostAux(Graph graph, bool *C, int n, int *col);

int BruteForceEdgeCon(EdgeConGraph graph)
{
    Graph g = getGraph(graph);
    int numHeteregeneousEdges = getNumHeteregeneousEdges(graph);
    int heterogeneousEdges[numHeteregeneousEdges];
    int N = getNumComponents(graph);
    int maxSubHt = binCoeff(numHeteregeneousEdges, N);
    int numSubHt;
    bool subSetOfHt[orderG(g) * orderG(g)];
    bool valid;

    if (maxSubHt == 0) return -1;

    getHeterogeneousEdges(graph, heterogeneousEdges);

    //printf("[DEBUG] Total of subSets of size %d of Ht = %d\n", N, maxSubHt);
    for (int k = 1; k <= N; k++)
    {
        valid = true;
        numSubHt = 0;
        //printf("[DEBUG] Current k=%d\n", k);
        while (valid && numSubHt < maxSubHt) // equiv ForEach C
        {
            memset(subSetOfHt, 0, sizeof subSetOfHt);
            getSubSetOfHeterogeneousEdges(heterogeneousEdges, numHeteregeneousEdges, N, numSubHt, subSetOfHt);

            int cost = MaxCost(g, subSetOfHt);
            //printf("[DEBUG] cost=%d\n", cost);
            if (cost > 0 && cost > k)
                valid = false;

            numSubHt++;
        }
        if (valid)
        {
            //printf("[DEBUG] K=%d\n", k);
            return k;
        }
    }
    //printf("[DEBUG] N=%d\n", N);
    return N;
}

int MaxCost(Graph graph, bool *C)
{
    int max = 0;
    int maxPrime;
    int col[orderG(graph)];
    for (int node = 0; node < orderG(graph); node++)
    {
        memset(col, WHITE, sizeof col);
        maxPrime = MaxCostAux(graph, C, node, col);

        /* If there is a WHITE Node, then return 0 */
        for (int n = 0; n < orderG(graph); n++)
            if (col[n] == WHITE)
                return 0;

        if (maxPrime > max)
            max = maxPrime;
    }
    return max;
}

int MaxCostAux(Graph graph, bool *C, int n, int *col)
{
    int queueNodesMaxSize = orderG(graph);
    int queueNodes[queueNodesMaxSize];
    int queueNodesRear = -1;
    int queueNodesFront = -1; 

    int cost[orderG(graph)];
    memset(cost, 0, sizeof cost);

    col[n] = GREY;
    QueueAdd(n, queueNodes, &queueNodesRear, &queueNodesFront, queueNodesMaxSize);

    int x;
    while (queueNodesRear >= queueNodesFront) /* While not empty */
    {
        x = QueuePop(queueNodes, &queueNodesRear, &queueNodesFront);
        if (x == -1) return -1;

        for (int y = 0; y < orderG(graph); y++)
        {
            if (isEdge(graph, x, y))
            {
                if (col[y] == WHITE)
                {
                    cost[y] = cost[x];

                    /* If (x, y) includes in C */
                    if (C[x * orderG(graph) + y] == 1)
                        cost[y] += 1;

                    col[y] = GREY;
                    QueueAdd(y, queueNodes, &queueNodesRear, &queueNodesFront, queueNodesMaxSize);
                }
            }
        }
        col[x] = BLACK;
    }
    return maxOfArray(cost, orderG(graph));
}
