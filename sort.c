#include <stdint.h>

#define N 12

void swap(int* x, int* y){
	int aux = *x;
	*x = *y;
	*y = aux;
}

void sort (int8_t a[], int size) {
	/*Bubble sort algorithm*/
	int i, j;
	for(i = 0; i < size - 1; i++){
		for(j = 0; j < size - i - 1; j++){
			if(a[j] > a[j + 1]){
				swap(&a[j], &a[j + 1]);
			}
		}
	}
}

void checkSort() {

 	int8_t	array[N];
 	int i;
	for (i = 0; i < N; ++i){
               // Assume numbers in array are integers in range [0,16]
		__CPROVER_assume(array[i] >= 0 && array[i] <= 16);
	}

	sort (array, N);

	for(int i = 0; i < N - 1; i++){
		__CPROVER_assert(array[i] <= array[i + 1], "array sorted");
	}

	// write the assertions to check that the array is sorted

}

int main(){
	/*int array1[6] = {0, 16, 5, 10, 6, 2};
	int array2[8] = {1, 5, 3, 8, 12, 4, 2, 16};
	int array3[10] = {6, 1, 4, 0, 16, 5, 8, 11, 15, 12};
	int array4[12] = {6, 1, 4, 0, 16, 5, 8, 11, 15, 12, 16, 13};*/
//	checkSort();
}
