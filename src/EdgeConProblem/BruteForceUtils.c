#include <stdlib.h>
#include <stdio.h>

#include "BruteForceUtils.h"
#include "Graph.h"

int queueAdd(int data, int *queue, int *rear, int *front, int maxSize)
{
    if (*rear != maxSize - 1)   // If there is no queue overflow
    {
        if (*front == -1)   // If queue is initially empty
            *front = 0;
        *rear += 1;
        queue[*rear] = data;
    }
}

int queuePop(int *queue, int *rear, int *front)
{
    if (*front == -1 || *front > *rear) // If there is a queue underflow
        return -1;

    int data;
    data = queue[*front];
    *front += 1;
    return data;
}

int binCoeff(int n, int k)
{
    if (k < 0 || k > n)
        return 0;
    if (k == 0 || k == n)
        return 1;

    k = min(k, n - k);  // Take advantage of symmetry
    int c;
    
    c = 1;
    for (int i = 0; i < k; i++)
    {
        c = c * (n - i) / (i + 1);
    }
    
    return c;
}

void getCombination(int arr[], int output[], int n, int r, int m)
{
    // A temporary array to store all combinations one by one
    int data[r];
    int val;
    int *c;

    val = 0;
    *c = &val;
    // Print all combinations using the temporary array 'data[]'
    combinationUtil(arr, output, n, r, 0, data, 0, c, m);
}

void combinationUtil(int arr[], int output[], int n, int r, int index, int data[], int i, int *c, int m)
{
    if (*c > m)
        return;

    // If current combination is ready, print it
    if (index == r)
    {
        if (m == *c)
        {
            for (int j = 0; j < r; j++)
            {
                output[j] = data[j];
            }
        }
        ++(*c);
        return;
    }

    // When no more elements are there to put in data[]
    if (i >= n)
        return;

    // Current combination is included, put next at next location
    data[index] = arr[i];
    combinationUtil(arr, output, n, r, index + 1, data, i + 1, c, m);

    // Current combination is excluded, replace it with next one
    // (Note that i + 1 is passed, but index is not changed)
    combinationUtil(arr, output, n, r, index, data, i + 1, c, m);
}

int maxOfArray(int *arr, int n)
{
    int max;

    max = arr[0];
    for (int i = 1; i < n; i++)
    {
        if (arr[i] > max)
            max = arr[i];
    }
    return max;
}

int min(int a, int b)
{
    if (a > b)
        return b;
    return a;
}

void getHeterogeneousEdges(EdgeConGraph graph, int *output)
{
    int cpt;
    Graph g;

    cpt = 0;
    g = getGraph(graph);
    for (int u = 0; u < orderG(g); u++)
    {
        for (int v = u + 1; v < orderG(g); v++)
        {
            if (isEdgeHeterogeneous(graph, u, v))
            {
                int pos;
                pos = u * orderG(g) + v;
                output[cpt] = pos;
                cpt++;
            }
        }
    }
}

void getSubSetOfHeterogeneousEdges(int *heterogeneousEdges, int n, int size, int numSubHt, bool *output)
{
    int combination[size];

    getCombination(heterogeneousEdges, combination, n, size, numSubHt);
    for (int i = 0; i < size; i++)
        output[combination[i]] = true;
}

void updateGraphTranslators(EdgeConGraph graph, bool* arr) {
    Graph g;
    
    g = getGraph(graph);
    for (int u = 0; u < orderG(g); u++)
    {
        for (int v = u + 1; v < orderG(g); v++)
        {
            if (isEdgeHeterogeneous(graph, u, v))
            {
                int pos;
                pos = u * orderG(g) + v;
                if (arr[pos] == 1)
                    addTranslator(graph, u, v);
            }
        }
    }
}