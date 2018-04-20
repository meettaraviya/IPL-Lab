
int *maxn;


int* factorial(int* a, int* b){
	int *d, *c;
	*d = *c;
	while (*d<*a){
		*c = *c * *d;
		*d = *d + 1;
	}
	return c;
}


void main(){
	int *n, *x, *y;
	float *t;
	*y = 1;
	*n = 3;
	*maxn = 100000;
	x = factorial(n, y);
}