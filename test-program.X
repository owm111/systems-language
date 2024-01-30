i64, i64
divmod(i64 num, i64 den)
{
	i64 quot;
	i64 rem;

	quot = num / den;
	rem = num % den;
	return quot, rem;
}

i64
computesum(i64 n, u1 inclusive)
{
	i64 result;
	i64 i;

	result = i = 0;
	while (i < n) {
		result = result + i;
		i = i + 1;
	}
	if (inclusive)
		result = result + i;
	return result;
}

i64
recursivesum(i64 n)
{
	if (n == 0)
		return 0;
	return recursivesum(n - 1) + n;
}

u0
arraytest(u0)
{
	i64 i;
	i64 sum;
	i64 array[10];

	i = 0;
	while (i < 10) {
		array[i] = i;
		i = i + 1;
	}
	sum = i = 0;
	while (i < 10) {
		sum = array[i] + sum;
		printf("array[%d] = %d (%d)\n", i, array[i], sum);
		i = i + 1;
	}
	printf("sum of [0 .. 10] via array: %d\n", sum);
	return;
}

u0
matrixtest(u0)
{
	i64 i; i64 j; i64 k;
	i64 matrix[2][3];

	i = k = 0;
	while (i < 2) {
		j = 0;
		while (j < 3) {
			matrix[i][j] = k;
			k = k + 1;
			j = j + 1;
		}
		i = i + 1;
	}

	i = 0;
	while (i < 2) {
		j = 0;
		while (j < 3) {
			printf("matrix[%d][%d] = %d\n", i, j, matrix[i][j]);
			j = j + 1;
		}
		i = i + 1;
	}
}

i32
main(u0)
{
	i64 sum;
	u1 broken;

	i64 n; i64 d; i64 q; i64 r;
	n = 123;
	d = 19;
	q, r = divmod(n, d);
	printf("%d / %d = %d r %d\n", n, d, q, r);

	sum = computesum(10, cast(1, u1));
	printf("sum via loop [0, 10] = %d\n", sum);
	sum = recursivesum(10);
	printf("sum via recursion [0, 10] = %d\n", sum);
	broken = sum != 55;

	matrixtest();

	return cast(broken, i32);
}
