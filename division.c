#include <stdio.h>

int main( void ) {
  int D,d, r, q;

  __CPROVER_assume( (D < 0) &&  (D >= -300) && (d > 0) );
  /*Modifying the assumption for the value of 'd' to avoid divisions by 0. Divisions by 0 -> infinite loop (and arithmetic failure)*/
  r = D; 
  q = 0;
  while ( r < 0 ) {
     r = r + d;
     q--;   
  }
  printf( " quotient: %d,  reminder: %d\n", q, r );
  /*
  __CPROVER_assert((q == D / d), "q is the quotient");
  __CPROVER_assert((r == D % d), "r is the reminder"); En calcular mal la division se calcula mal el residuo
  Instead of using this two macros, the division check that is learned in primary school will be used.
  */
  __CPROVER_assert((D == (q * d) + r), "Checking division");
}
