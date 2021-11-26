#include "EdgeConGraph.h"

/**
 * @brief Get the heterogeneous edges from @p graph and put them into @p output
 * 
 * @param graph EdgeConGraph
 * @param output Array
 */
void getHeterogeneousEdges(EdgeConGraph graph, int* output);

/**
 * @brief Get subset of the heterogeneous edges from @p heterogeneousEdges and put them into @p output
 * 
 * @param heterogeneousEdges Array of heterogeneous edges
 * @param n Int size of @p heterogeneousEdges
 * @param size Int size of the subset wanted
 * @param numSubHt Int Index of the subset wanted
 * @param output Array to store the result
 */
void getSubSetOfHeterogeneousEdges(int* heterogeneousEdges, int n, int size, int numSubHt, bool* output);

/**
 * @brief Update the translators
 * 
 * @param graph EdgeConGraph to update
 * @param arr An array that represents the translators
 */
void updateGraphTranslators(EdgeConGraph graph, bool* arr);

/**
 * @brief Binomial coefficient. From https://en.wikipedia.org/wiki/Binomial_coefficient#In_programming_languages
 * 
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
 * @return Return the maximum value of @p arr.
 */
int maxOfArray(int *arr, int n);

/**
 * @param a
 * @param b
 * 
 * @return Return the minimal value between @p a and @p b.
 */
int min(int a, int b);

/**
 * @brief Get the m-nth combinations of a given size. Mainly uses combinationUtil(). From https://www.geeksforgeeks.org/print-subsets-given-size-set/ 
 * 
 * @param arr An array containing the set
 * @param output An array to store the result
 * @param n Size of arr
 * @param r Size of all combinations
 * @param m Index of the wanted combination
 */
void getCombination(int arr[], int output[], int n, int r, int m);

/**
 * 
 * @param arr An array containing the set
 * @param output An array to store the result
 * @param n Size of @p arr
 * @param r Size of all combinations
 * @param index Current index in @p data
 * @param data Temporary array to store current combination
 * @param i Index of current element in arr[]
 * @param c Counter of the current element
 * @param m Index of the wanted combination
 */
void combinationUtil(int arr[], int output[], int n, int r, int index, int data[], int i, int *c, int m);

/**
 * @brief Add an element to the end of the queue. From : https://www.sanfoundry.com/c-program-queue-using-array/
 * 
 * @param data Int to add
 * @param queue Array representing the queue
 * @param rear Pointer to the end of the queue
 * @param front Pointer to the start of the queue
 * @param maxSize Int maximum size of @p queue, size of the array @p queue
 */
int queueAdd(int data, int *queue, int *rear, int *front, int maxSize);

/**
 * @brief Return the first element of the queue, and remove from it. From : https://www.sanfoundry.com/c-program-queue-using-array/
 * 
 * @param queue Array representing the queue
 * @param rear Pointer to the end of the queue
 * @param front Pointer to the start of the queue
 * 
 * @return the first element of @p queue
 */
int queuePop(int *queue, int *rear, int *front);