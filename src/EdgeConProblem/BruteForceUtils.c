#include "BruteForceUtils.h"
#include "Graph.h"
#include <stdlib.h>
#include <stdio.h>

int QueueAdd(int data, int *queue, int *rear, int *front, int maxSize)
{
    if (*rear != maxSize - 1) /* If queue not overflow */
    {
        if (*front == -1) /*If queue is initially empty */
            *front = 0;
        *rear += 1;
        queue[*rear] = data;
    }
}

int QueuePop(int *queue, int *rear, int *front)
{
    if (*front == -1 || *front > *rear) /* If queue underflow */
        return -1;

    int data = queue[*front];
    *front += 1;
    return data;
}

int binCoeff(int n, int k)
{
    if (k < 0 || k > n)
        return 0;
    if (k == 0 || k == n)
        return 1;

    k = min(k, n - k); // Take advantage of symmetry

    int c = 1;
    for (int i = 0; i < k; i++)
    {
        c = c * (n - i) / (i + 1);
    }
    return c;
}

void getCombination(int arr[], int output[], int n, int r, int m)
{
    // A temporary array to store all combination
    // one by one
    int data[r];
    int val = 0;
    int *c = &val;

    // Print all combination using temporary array 'data[]'
    combinationUtil(arr, output, n, r, 0, data, 0, c, m);
}

void combinationUtil(int arr[], int output[], int n, int r, int index, int data[], int i, int *c, int m)
{

    if (*c > m)
        return;

    // Current combination is ready, print it
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

    // current is included, put next at next location
    data[index] = arr[i];
    combinationUtil(arr, output, n, r, index + 1, data, i + 1, c, m);

    // current is excluded, replace it with next
    // (Note that i+1 is passed, but index is not
    // changed)
    combinationUtil(arr, output, n, r, index, data, i + 1, c, m);
}

int maxOfArray(int *arr, int n)
{
    int max = arr[0];
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
    int cpt = 0;
    Graph g = getGraph(graph);
    for (int u = 0; u < orderG(g); u++)
    {
        for (int v = u + 1; v < orderG(g); v++)
        {
            if (isEdgeHeterogeneous(graph, u, v))
            {
                int pos = u * orderG(g) + v;
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