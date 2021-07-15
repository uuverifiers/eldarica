# 1 "/tmp/tmp.iQTEZnXQj2.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.iQTEZnXQj2.c"
void errorFn(){assert(0);}

extern int unknown1();
int unknown2();
int unknown3();
int unknown4();





void main(){

  int /*@  predicates{i>=0} @*/ i, /*@  predicates{n>=0,n>=i,n>i} @*/ n, /*@  predicates{a<=i,a>=i} predicates_tpl{0==0} terms_tpl{a-2*i,a-i} @*/ a, /*@  predicates{b<=a,b<=i,b>=a,b>=i} terms_tpl{2*b-2*a,2*b-a,b-2*a,b-2*i,b-a,b-i} @*/ b;
  assume(n >= 0);
  i = 0; a = 0; b = 0;
  while(i < n){
    if(unknown1()){
      a = a+1;
      b = b+2;
    } else {
      a = a+2;
      b = b+1;
    }
    i = i+1;
  }
  if(!(a+b == 3*n))
  errorFn();
}
