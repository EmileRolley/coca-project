#include "EdgeConGraph.h"



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

int QueueAdd(int data, int *queue, int *rear, int *front, int maxSize);

int QueuePop(int *queue, int *rear, int *front);

void getHeterogeneousEdges(EdgeConGraph graph, int* arr);

void getSubSetOfHeterogeneousEdges(int* heterogeneousEdges, int n, int size, int numSubHt, bool* output);