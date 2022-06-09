#include <stdio.h>

int main( void ) {
  int D,d, r, q;

  __CPROVER_assume( (D < 0) &&  (D >= -300) && (d > 0) );
  r = D; 
  q = 0;
  while ( r < 0 ) {
     r = r + d;
     q--;   
  }
  printf( " quotient: %d,  reminder: %d\n", q, r );
  __CPROVER_assert((q == D/d), "q is the quotient");
  __CPROVER_assert((r == d%d), "r is the reminder");
}
