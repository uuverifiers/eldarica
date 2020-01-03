# 1 "/tmp/tmp.iQTEZnXQj2.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.iQTEZnXQj2.c"
void errorFn(){assert(0);}







void main(){
  int i,/*@  predicates{k<=i,k>=1,k>=i} predicates_tpl{0==0} terms_tpl{k-i} @*/ k,/*@  predicates{n>=i,n>=k,n>i,n>k} @*/ n,/*@  predicates{l<=i,l>0} @*/ l;


  assume(l>0);

  for(k=1;k<n;k++){
    for(i=l;i<n;i++){
    }
    for(i=l;i<n;i++){
      if(!(1<=i))
  errorFn();
    }
  }

}
