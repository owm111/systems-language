u0
printarray(i64 length, ref i64[999] array)
{
	i64 i;

	i = 0;
	while (i < 10) {
		printf("%d, ", array[i]);
		i = i + 1;
	}
	printf("\n",);
}

u0
initarray(ref i64[10] array)
{
	array[0] = 324; array[1] = 738; array[2] = 392; array[3] = 638;
	array[4] = 281; array[5] = 847; array[6] = 173; array[7] = 638;
	array[8] = 594; array[9] = 284;
}

i64, i64
swap(i64 x, i64 y)
{
	return y, x;
}

i64, i64
bubble(i64 x, i64 y)
{
	if (x > y)
		return y, x;
	return x, y;
}

u0
bubblesort(i64 length, ref i64[999] array)
{
	i64 i;
	i64 j;

	i = 0;
	while (i < length) {
		j = 1;
		while (j < length) {
			array[j - 1], array[j] = bubble(array[j - 1], array[j]);
			j = j + 1;
		}
		i = i + 1;
	}
}

i64
partition(ref i64[999] array, i64 lo, i64 hi)
{
	i64 pivot;
	i64 i;
	i64 j;

	pivot = array[lo];
	i = lo - 1;
	j = hi + 1;
	while (1 == 1) {
		i = i + 1;
		while (array[i] < pivot)
			i = i + 1;
		j = j - 1;
		while (array[j] > pivot)
			j = j - 1;
		if (i >= j)
			return j;
		array[i], array[j] = swap(array[i], array[j]);
	}
}

u0
quicksort(ref i64[999] array, i64 lo, i64 hi)
{
	i64 p;

	if (lo < 0) return;
	if (hi < 0) return;
	if (lo >= hi) return;
	p = partition(array, lo, hi);
	quicksort(array, lo, p);
	quicksort(array, p + 1, hi);
}

i32
main(u0)
{
	i64 array[10];

	printf("Bubblesort\n",);
	initarray(array);
	printarray(10, array);
	bubblesort(10, array);
	printarray(10, array);

	printf("Quicksort\n",);
	initarray(array);
	printarray(10, array);
	quicksort(array, 0, 10);
	printarray(10, array);

	return cast(0, i32);
}