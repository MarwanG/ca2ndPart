#define N 10
int A[N] = {23, 45, -6, 120, 2, 11, 23, -5, 12, 14};
int B[N] = {13, 5, -16, 12, 24, 115, -123, -55, 57, 0};
int C[N];
int D[N];

void sum(int tab1[], int tab2[], int tab3[], int size)
{
  int i;
  for (i = 0; i < size; i++){
    tab3[i] = tab1[i]  + tab2[i]; 
  }
  return;
}
int max_min_tab(int a[], int b[], int c[], int d[], int size){
  int i;
  for (i = 0; i < size; i++){
    if (a[i] < b[i]){
      c[i] = b[i];
      d[i] = a[i];
    }
    else {
      c[i] = a[i];
      d[i] = b[i];
    }
  }
  return 0;
}

int mat_mul(int a[N][N], int b[N][N], int c[N][N]){
  int i, j, k;
  for (i = 0;  i < N; i++)
     for (j = 0;  i < N; i++)
       c[i][j] = 0;

  for (i = 0;  i < N; i++)
     for (j = 0;  i < N; i++)
       for (k = 0;  i < N; i++)
	 c[i][j] += a[i][k] * b[k][j];

  return 1;
}

int main(int argc, char ** argv){

  sum(A, B, C, N);
  printf("%d\n", max_min_tab(A, B, C, D, N));
 
  return 0;
}
