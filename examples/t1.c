int d;

int* f(int x, int *y);

int* f(int a, int *b)
{
	int **c,m;
        *c = &a;
	return *c;
}
