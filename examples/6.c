int* d;

int* f1(int x, int *y);

int f2(int x, int *y);

float f3(int x, int *y, float *c, float *d);

void f4(int a, int b, int x, int y, int a1, int b1, int x1, int y1, int a2, int b2, int x2, int y2, int a3, int b3, int x3, int y3);
void f4(int a, int b, int x, int y, int a1, int b1, int x1, int y1, int a2, int b2, int x2, int y2, int a3, int b3, int x3, int y3){

	int **c, m;
}

void main() {
	int *rt;

	if (3 <= 5 ) {
		*rt = 1;
	} else {
		*rt = 2;
	}


	while (! (3 < 5) )
		if (3 > 5 && 3 >= 5 || (*rt <= *rt + 1) ) {
			*rt = 3;
			if (3 != 5 ) {
				*rt = 1;
				if (3 == 5 ) {
					*rt = 1;
				} else {
					*rt = 2;
				}

			} else {
				*rt = 2;
				if (3 >= 5 ) {
					*rt = 1;
				} else {
					*rt = 2;
				}
			}

		}


}
int* f1(int a, int *b)
{
	int **c, m;
	*c = &m;
	**c = **c * *d / *d - *d;
	return *c;
}


int f2(int a, int *b)
{
	int **c, m;
	float *b1;
	*c = &m;
	f2(**c + *b,*c);
	**c = f2(**c + *b,*c);
	*c = f1(**c + *b,*c);
	*b1 = f3(**c + *b,*c,b1,b1);
	**c = **c * *d / *d - *d;
	return **c + *d;
}

float f3(int a, int *b, float *x, float *y)
{
	int **c, m;
	*c = &m;
	f1(*b, b);
	*c = f1(*b, b);
	f1(*b, b);
	**c = **c * *d / *d - *d;
	f4(*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b, *b+*b);
	return *x + *y;
}
