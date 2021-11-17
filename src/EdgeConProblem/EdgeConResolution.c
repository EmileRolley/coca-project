#include "EdgeConResolution.h"
#include "Graph.h"
#include <stdlib.h>
#include <stdio.h>

#include <sys/queue.h>

const int WHITE = 0;
const int GREY = 1;
const int BLACK = 2;

struct entry
{
    int data;
    STAILQ_ENTRY(entry)
    entries; /* Singly linked tail queue */
};
STAILQ_HEAD(stailhead, entry);

int MaxCost(Graph graph, bool *C);
int MaxCostAux(Graph graph, bool *C, int n, int *col);

/**
 * @param n
 * @param k
 * 
 * @pre @p n > @p k
 * 
 * @return The binomial coefficient.
 */
int binCoeff(int n, int k);

/**
 * @param arr An array of int
 * @param n Size of @p arr
 * 
 * @return Return the max of @p arr.
 */
int maxOfArray(int *arr, int n);

/**
 * @param a
 * @param b
 * 
 * @return Return the min between @p a and @p b.
 */
int min(int a, int b);

/**
 * @param data Data to add to the Queue
 * @param head The Queue
 */
void QueueAdd(int data, struct stailhead *head);

/**
 * @param head The Queue
 * 
 * @return Return the first element of the Queue @p head and remove it.
 */
int QueuePop(struct stailhead *head);

/**
 * @brief Free the Queue
 * 
 * @param head The Queue
 */
void QueueFree(struct stailhead *head);

/**
 * @brief Get the m-nth combination of a given size. Mainly uses combinationUtil()
 * 
 * @param arr An array containing the set
 * @param output An array to store the result
 * @param n Size of arr
 * @param r Size of all combinations
 * @param m Index of the wanted combination
 */
void getCombination(int arr[], int output[], int n, int r, int m);

/* arr[]  ---> Input Array
   n      ---> Size of input array
   r      ---> Size of a combination to be printed
   index  ---> Current index in data[]
   data[] ---> Temporary array to store current combination
   i      ---> index of current element in arr[]     */

/**
 * 
 * @param arr An array containing the set
 * @param output An array to store the result
 * @param n Size of arr
 * @param r Size of all combinations
 * @param index Current index in @p data
 * @param data Temporary array to store current combination
 * @param i Index of current element in arr[]
 * @param c Counter of the current element
 * @param m Index of the wanted combination
 */
void combinationUtil(int arr[], int output[], int n, int r, int index, int data[], int i, int *c, int m);




int BruteForceEdgeCon(EdgeConGraph graph)
{
    Graph g = getGraph(graph);

    int set[getNumHeteregeneousEdges(graph)];
    int cpt = 0;
    for (int u = 0; u < orderG(g); u++)
    {
        for (int v = u + 1; v < orderG(g); v++)
        {
            if (isEdgeHeterogeneous(graph, u, v))
            {
                int pos = u * orderG(g) + v;
                set[cpt] = pos;
                cpt++;
            }
        }
    }

    int N = getNumComponents(graph);
    int maxSubHt = binCoeff(getNumHeteregeneousEdges(graph), N); // The number of possible combination. Almost infinite, replace by 10 000
    printf("Total of subSets of size %d of Ht = %d\n", N, maxSubHt);
    for (int k = 1; k <= N; k++)
    {
        bool valid = true;
        int numSubHt = 0;
        printf("Current k=%d\n", k);
        while (valid && numSubHt < maxSubHt) // equiv ForEach C
        {
            int *output = malloc(N * sizeof(int));
            getCombination(set, output, getNumHeteregeneousEdges(graph), N, numSubHt);

            bool *subSetOfHt = (bool *)calloc(orderG(g) * orderG(g), sizeof(bool));
            for (int i = 0; i < N; i++)
                subSetOfHt[output[i]] = true;

            int cost = MaxCost(g, subSetOfHt);
            if (cost > 0 && cost > k)
                valid = false;

            numSubHt++;
            free(subSetOfHt);
            free(output);
        }
        if (valid)
        {
            printf("K=%d\n", k);
            //free(set);
            return k;
        }
    }
    printf("N=%d\n", N);
    return N;
}

int MaxCost(Graph graph, bool *C)
{
    int max = 0;
    for (int node = 0; node < orderG(graph); node++)
    {
        /* Color associated at each node */
        int *col = (int *)calloc(orderG(graph), sizeof(int));
        int maxPrime = MaxCostAux(graph, C, node, col);

        /* If there is a WHITE Node, then return 0 */
        for (int n = 0; n < orderG(graph); n++)
        {
            if (col[n] == WHITE)
            {
                free(col);
                return 0;
            }
        }
        if (maxPrime > max)
            max = maxPrime;

        free(col);
    }
    return max;
}

int MaxCostAux(Graph graph, bool *C, int n, int *col)
{
    /* Init FIFO Queue */
    struct entry *elem;
    struct stailhead head;
    STAILQ_INIT(&head);

    /* Cost associated at each node */
    int *cost = calloc(orderG(graph), sizeof(int));

    col[n] = GREY;
    QueueAdd(n, &head);

    int x;
    while (!STAILQ_EMPTY(&head))
    {
        x = QueuePop(&head);
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
                    QueueAdd(y, &head);
                }
            }
        }
        col[x] = BLACK;
    }

    int m = maxOfArray(cost, orderG(graph));

    QueueFree(&head);
    free(cost);

    return m;
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
        //printf("a=%d\n", arr[i]);
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

void QueueAdd(int data, struct stailhead *head)
{
    struct entry *elem;
    elem = malloc(sizeof(struct entry));
    if (elem)
    {
        elem->data = data;
    }
    STAILQ_INSERT_TAIL(head, elem, entries);
}

int QueuePop(struct stailhead *head)
{
    /* Return -1 if queue is empty */
    if (STAILQ_EMPTY(head))
        return -1;

    /* Get the first element then remove it from the queue */
    struct entry *elem = STAILQ_FIRST(head);
    STAILQ_REMOVE_HEAD(head, entries);

    return elem->data;
}

void QueueFree(struct stailhead *head)
{
    struct entry *elem1 = STAILQ_FIRST(head);
    struct entry *elem2;

    while (elem1 != NULL)
    {
        elem2 = STAILQ_NEXT(elem1, entries);
        free(elem1);
        elem1 = elem2;
    }
}