#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <error.h>
#include <math.h>
#include "f2_poly.h"
#include "arithm.h"
#include "lfsr.h"

#ifdef __GNUC__

typedef union {
  uint64_t t64;
  uint32_t t32[2];
  uint16_t t16[4];
  uint8_t t8[8];
} bytes_array

/* clzll: GCC builtin function returning the number of leading-0 for unsigned long long */
/* clz: works for 32bits integer */
/* clz(l|ll): works for 64bit integer */
int8_t
f2_poly_deg(f2_poly_t p){
#ifdef WITH_8BITS
  bytes_array ba;  ba.t64[0] = 0; ba.t8[3] = p;
  return (p == ZERO) ? ZERO : __builtin_clz(p.t32)-1;
#elif defined WITH_16BITS
  bytes_array ba;  ba.t64[0] = 0;  ba.t16[1] = p;
  return (p == ZERO) ? ZERO : __builtin_clz(p)-1;
#elif defined WITH_32BITS
  return (p == ZERO) ? ZERO : __builtin_clz(p)-1;
#elif defined WITH_64BITS
  return (p == ZERO) ? ZERO : __builtin_clzll(p)-1;
#endif
}
#else
/* Computes the degree of a polynomial */
/* by successively shifting the value representing the polynomial until the MSD is found */
/* return -1 if the polynomial is null */
int8_t
f2_poly_deg(f2_poly_t p){
  int8_t i = LEN-1 ;
  if (p == ZERO) return -1;
  while (NTH_BIT_IS_ZERO(p,i)) {i--;};
  return i;
}

/* Pretty printer for polynomial */
void
f2_poly_print(f2_poly_t p, const char c , FILE * fd){
  char fmt_xn[] = {" + %c^%d", ""};
  char fmt_x1[] = {" + %c", ""};
  char fmt_x0[] = {" + 1", ""};
  int8_t nn_MSD = f2_poly_deg(p);
  fprintf(fd, "%c^%d ", c, nn_msd);

  for (int i = nn_MSD-1; i >= 0; i--)
    fprintf(fd, fmt_xn[GET_NTH_BIT(p,i)], c, i);
  
  fprintf(fd, fmt_x1[GET_NTH_BIT(p,1)]);
  fprintf(fd, fmt_x0[GET_NTH_BIT(p,0)]);
}

/* Compute the rest of the euclidian division*/
f2_poly_t
f2_poly_rem(f2_poly_t p, f2_poly_t q) {
  if (IS_NULL(q)) return 0;
  if (p < q) return p; // equivalent to deg_P < deg_Q since they are integers
  
  f2_poly_t res = p;
  int8_t deg_q = f2_poly_deg(q);
  int8_t deg_p = f2_poly_deg(p);
  int8_t deg_diff = deg_p - deg_q;
  
  while (res >= q) {
    res ^= (q << deg_diff);
    deg_diff = f2_poly_deg(res) - deg_q;
  }

  return res;
}

/* if (dnd){ // condition : dnd is not 0                           */
/*      if(f2_poly_deg(dnd)< f2_poly_deg(der)){                    */
/*        return dnd ;                                             */
/*      }                                                          */
/* ...                                                             */
/* } else {                                                        */
/*      return 0 ; */
/* } */

/* Computes the division between two polynomials */
/* inputs: f2_poly_t dnd, der*/
/* outputs: f2_poly_t *R, *Q */
f2_poly_t
f2_poly_div(f2_poly_t * R ,f2_poly_t * Q , f2_poly_t dnd, f2_poly_t der){
  *Q = 0;
  *R = 0;

  int8_t deg_dnd = f2_poly_deg(dnd);
  int8_t deg_der = f2_poly_deg(der);
  int8_t deg_diff = f2_poly_deg(dnd);

  if (dnd == 0 || deg_dnd < deg_der) return dnd;

  f2_poly_t r = dnd, q = 0;
  
  while (deg_diff >= deg_der) {
    if (NTH_BIT_IS_ONE(r, deg_diff)) {
      r ^= der << (deg_diff - deg_der);
      q ^= ONE << (deg_diff - deg_der);
    }
    deg_diff--;
  }
  
  *Q = q;
  *R = r;

  return 0;
}

/* Computes the GCD between two polynomials */
f2_poly_t
f2_poly_gcd(f2_poly_t a, f2_poly_t b){
  f2_poly_t d = 0;
  
  while (NTH_BIT_IS_ONE(a,0) && NTH_BIT_IS_ONE(b,0)) {
    a >>= ONE;
    b >>= ONE;
    d++;
  }

  while (NTH_BIT_IS_ONE(a,0)) { a >>= ONE; }
  while (NTH_BIT_IS_ONE(b,0)) { b >>= ONE; }

  while (a != b) {
    a -= (a < b) ? b : 0;
    b -= (a < b) ? 0 : a;
  }
  return a << d;
}

/* Computes a*x*b ? */
f2_poly_t
f2_poly_xtimes(f2_poly_t a , f2_poly_t b){ 
  /* Multiplies by the monomial X is like shifting to the right */
  return f2_poly_rem(a>>1 , b); 
}

/* Computes a*b % n ? */
f2_poly_t
f2_poly_times(f2_poly_t a, f2_poly_t b , f2_poly_t n){
  f2_poly_t res = 0;
  int8_t deg_b = f2_poly_deg(b);

  for (int i = 0; i <= deg_b; i++) {
    if (NTH_BIT_IS_ONE(b,i)) res ^= f2_poly_rem(a<<i, n);
  }
  return res;
}

/* Computes b^(2^n) ? */
f2_poly_t
f2_poly_x2n(size_t pow, f2_poly_t b){
  f2_poly_t x = 2; 
  for(int i = 0; i < pow ; i++){ 
    x = f2_poly_times(x,x,b); 
  }
  return x ;
}

#ifdef __GNUC__
/* Computes the parity of the polynomial */
f2_poly_t
f2_poly_parity(f2_poly_t P){
#ifdef WITH_8BITS
  return __builtin_parity(P);
#elif defined WITH_16BITS
  return __builtin_parity(P);
#elif defined WITH_32BITS
  return __builtin_parity(P);
#elif defined WITH_64BITS
  return __builtin_parityll(P);
#endif
  return __builtin_parityll(P);
}
#else
/* Computes the parity of the polynomial */
/* Equivalent to computing the rest of the euclidian division by X+1 */
f2_poly_t
f2_poly_parity(f2_poly_t P){
  return f2_poly_rem(P,3);
}
#endif

/* Derives a polynomial */
/* Equivalent to shifting to the left and to setting even bits to 0 */
f2_poly_t
f2_poly_derive(f2_poly_t P){
  return((P&UNZERO)>>1);
}

/* Computes P^n ? */
f2_poly_t
f2_poly_xn(size_t n, f2_poly_t P){
  f2_poly_t res = 1;
  f2_poly_t tmp = 2;
  for (int i = 0 ; i < n ; i++) {
    if ( n&1 ) {
      res = f2_poly_times(res, tmp, P);
    }
    tmp = f2_poly_times(tmp, tmp, P);
    n >>= 1;
  }
  return res;
}

#ifdef __GNUC__
uint8_t ReverseBitsInByte(uint8_t v) {
  return (v * 0x0202020202ULL & 0x010884422010ULL) % 1023;
}

f2_poly_t
f2_poly_recip(f2_poly_t P) {
  bytes_array ba;  ba.t64[0];
#ifdef WITH_8BITS
  return ReverseBitsInByte(P);
#elif defined WITH_16BITS
  bytes_array ba;  ba.t16[0] = P;
#elif defined WITH_32BITS
  bytes_array ba;  ba.t32[0] = P;
#elif defined WITH_64BITS
  bytes_array ba;  ba.t64 = P;
#endif
  for (size_t i = 0; i < sizeof(P); i++)
    ba.t8[i] = ReverseBitsInByte(ba.t8[i]);
#elif defined WITH_16BITS
  return ba.t16[0];
#elif defined WITH_32BITS
  return ba.t32[0];
#elif defined WITH_64BITS
  return ba.t64;
#endif
}
#else
/* Computes the reciprocal polynomial */
f2_poly_t
f2_poly_recip(f2_poly_t P){
  size_t taille = f2_poly_deg(P); 
  f2_poly_t res = 0 ; 
  for(int i = taille ; i > 0 ; i--){ 
    res ^= P&(1<<i)<<(taille-i) ; 
  }
  return res ;
}
#endif

/* Return a random polynomial */
/* Or using a Mersen twister */
f2_poly_t
f2_poly_random_inf(int8_t taille) {
  f2_poly_t ret = (f2_poly_t)rand();
  ret << 32;
  ret |= rand();
  return ret;
}

/* Return a random polynomial of size taille */
/* Or using a Mersen twister */
f2_poly_t
f2_poly_random(int8_t taille) {
  f2_poly_t ret = f2_poly_random_inf(taille);
  ret |= 1<<taille;
  return ret;
}


/* Checks if the polynomial is irreductible or not */
/* Returns 1 if it is irreductible and 0 otherwise */
int
f2_poly_irred(f2_poly_t p) {
  /* X is divisible by monomial X or the polynomial is divisible by X+1*/
  if (ITH_BIT_IS_ZERO(p,1) || f2_poly_parity(p) == 0) return 0;

  uint64_t tmp_n, pp;
  uint8_t deg_p = f2_poly_deg(deg_p);
  f2_poly_t X2n_X = f2_poly_x2n(deg_p, p) ^ (1 << 1), Xpn_X;

  if (!IS_NULL(X2n_X)) return 1;
  
  tmp_n = deg_p;
  while (tmp_n > 1) {
    pp = pp_diviseur_premier(tmp_n);
    Xpn_X = f2_poly_x2n(deg_p/pp,p) ^ (1<<1);
    if(f2_poly_gcd(Xpn_X,p) > 1) return 0 ;      
    tmp_n = tmp_n/pp ;
  }
  
  return 1;
}


/* Checks if the polynomial is prime ? */
int
f2_poly_primitive(f2_poly_t p){
  if(!f2_poly_irred(p)){ // on teste d'abord si le polynome est irreductible,
    return 0; //sinon, on retourne directement qu'il n'est pas primitif
  }
  size_t n = f2_poly_deg(p); //
  size_t tmp_n = (1ULL << n) - 1;
  uint64_t q;
  while (tmp_n > 1) { // Nous allons entamer une boucle pour tester chaque diviseur
    q = pp_diviseur_premier(tmp_n);
    if (f2_poly_xn(tmp_n/q, p) == 1) { // on regarde si le polynome
      return 0;
    }
    while (tmp_n%q == 0) {
      tmp_n /= q;
    }
  }
  return 1;
}
