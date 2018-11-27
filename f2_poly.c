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

#ifdef __GNUC__
/* clzll: GCC builtin function returning the number of leading-0 for unsigned long long */
int8_t
f2_poly_deg(f2_poly_t p){
  return (p == ZERO) ? ZERO : __builtin_clzll(p)-1;
}
#else
/* Computes the degree of a polynomial */
/* by successively shifting the value representing the polynomial until the MSD is found */
/* return -1 if the polynomial is null */
int8_t
f2_poly_deg(f2_poly_t p){
  int8_t i = LEN-1 ;
  if (p == 0x0) return -1;
  while (NTH_BIT_IS_ZERO(p,i)) {i--;};
  return i;
}

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

f2_poly_t
f2_poly_div(f2_poly_t * R ,f2_poly_t * Q , f2_poly_t dnd, f2_poly_t der){
  *Q = 0;
  *R = 0;

  if (dnd == 0 || dnd < der) return dnd;
  
  int8_t deg_dnd = f2_poly_deg(dnd);
  int8_t deg_der = f2_poly_deg(der);
  int8_t deg_diff = f2_poly_deg(dnd);

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

f2_poly_t
f2_poly_xtimes(f2_poly_t a , f2_poly_t b ){ //
  return f2_poly_rem(a>>1 , b); // muliplier par le monome X revient à effectuer un décalage vers la droite
}

f2_poly_t
f2_poly_times(f2_poly_t a, f2_poly_t b , f2_poly_t n){
  f2_poly_t res = 0;
  int8_t deg_b = f2_poly_deg(b);

  for (int i = 0; i <= deg_b; i++) {
    if (NTH_BIT_IS_ONE(b,i)) res ^= f2_poly_rem(a<<i, n);
  }
  return res;
}

f2_poly_t
f2_poly_x2n(size_t pow, f2_poly_t b){
  f2_poly_t x = 2; // Nous allons multiplier par un monome de degrés une puissance de 2, donc on initilise un polynome à x^2
  for(size_t i = 0; i < pow ; i++){ // Nous allons boucler sur la valeur de la puissance de 2
    x = f2_poly_times(x,x,b); // Et nous allons appliquer la fonction de multiplication sur x par x afin d'avoir des puissance de x en puissance de 2
  }
  return x ;
}

#ifdef __GNUC__
f2_poly_t
f2_poly_parity(f2_poly_t P){
  return __builtin_parityll(P);
}
#else
f2_poly_t
f2_poly_parity(f2_poly_t P){
  return f2_poly_rem(P,3); // Ici, on aurait pu faire de deux façon différente, Soit on rend le reste de la division euclidienne par X+1
                              // Soit on retourne la somme de tous les bits modulo 2 dans F2
}
#endif

f2_poly_t
f2_poly_derive(f2_poly_t P){
  return((P&UNZERO)>>1); // Ici, lorsque l'on dérive un polynome dans F2 c'est equivalent à décaler tous les bit d'une position
}                        // Sans oublier de mettre tous les bits en position pair à 0

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

f2_poly_t
f2_poly_recip(f2_poly_t P){
  size_t taille = f2_poly_deg(P); // On stock la taille du polynome dans une variable
  f2_poly_t res = 0 ; // Pour cette fonction nous devons uniquement lire et stocker ses bits en sens inverse
  for(int i = taille ; i > 0 ; i--){ // On entame donc une boucle sur la taille du polynome
    res ^= P&(1<<i)<<(taille-i) ; // res qui était initialisé à 0 est incrémenté en lisant les bits de P en sens inverse
  }
  return res ; // on retourne le polynome ainsi construit
}

f2_poly_t
f2_poly_recip(f2_poly_t P) {
  // reversing bits 
}

f2_poly_t
f2_poly_random_inf(size_t taille){
  f2_poly_t res = 0; // Nous initialisons le resulats à 0
  int alea ; // nous allons prendre une variable qui va gérer l'aléa
  srand(time(NULL)); // On Génère l'aléa grace a la fonction srand() et la fonction time()
  for(int i = 0 ; i< taille ; i++){ // Nous allons entamer une boucle
    alea = rand(); // choisir une valeur aléaoitre
    res += (alea % 2)<<i; // Et suivant que la variable choisie est pair ou impair (aléatoirement) on met un bit à 0 ou à 1
  }
  return res ; // on retourne ainsi le résultat
}

/* Or using a Mersen twister */
f2_poly_t
f2_poly_random_inf(int8_t taille) {
  f2_poly_t ret = (f2_poly_t)rand();
  ret << 32;
  ret |= rand();
  return ret;
}

f2_poly_t // Toute la premiere partie de la fonction est semblable à la précédente
f2_poly_random(size_t taille){
  f2_poly_t res = 0;
  int alea , i;
  srand(time(NULL));
  for( i = 0 ; i<= taille-1 ; i++){
    alea = rand();
    res += (alea % 2)<<i;
  }
  res += 1<<i ; // Pour être sûr que le polynom soit de degré exactement égale à taille, on ajoute le bit à la position "taille" (manuellement)
  return res ;  // On retourne le resultats
}


/* Or using a Mersen twister */
f2_poly_t
f2_poly_random(int8_t taille) {
  f2_poly_t ret = f2_poly_random_inf(taille);
  ret |= 1<<taille;
  return ret;
}


int
f2_poly_irred(f2_poly_t p){
  int deg_p = f2_poly_deg(p) ;// On Stocke la valeur du degré de p
  if(!(p&&1)){ // ici, le cas ou le polynom est divisble par le monome X
    return 0 ;
  }
  if(!f2_poly_parity(p)){ // Le cas ou le polynom est pair (divisible par X+1)
    return 0;
  }
  uint64_t tmp_n ; // tmp_n et pp sont des variables qui vont nous servir pour les critères de divisibilités
  uint64_t pp ;
  f2_poly_t X2n_X = f2_poly_x2n(deg_p,p) ^ (1<<1); // On construit le polynome X^2^n - X modulo P
  if (X2n_X == 0){ // le cas ou le polynome X^2^n - X est divisible par le polynome P
    tmp_n = deg_p ; //
    while(tmp_n>1){// Dans cette boucle nous allons lister tous les diviseur premiers du degré du polynome
      pp = pp_diviseur_premier(tmp_n);
      f2_poly_t Xpn_X = f2_poly_x2n(deg_p/pp,p) ^(1<<1) ; // tester si le polynome du TD est premier avec le polynome P
      if(f2_poly_gcd(Xpn_X,p)>1){ // Si un moment, nous avons que le GCD est plus grand que 1 alors il renvoie 0 (non irreductible)
        return 0 ;
      }
      tmp_n = tmp_n/pp ;
    }
  }
  return 1 ;// Si le polynome passe tous les tests décrits en TD alors il est irreductible dans F2
}


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
