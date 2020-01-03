# 1 "/tmp/tmp.iQTEZnXQj2.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.iQTEZnXQj2.c"
void errorFn(){assert(0);}

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main(int /*@  predicates{flag==0} predicates_tpl{0==0} @*/ flag)
{

 int x = 0;
 int /*@  predicates{y<=x,y>=x} terms_tpl{y-x} @*/ y = 0;

 int /*@  predicates{j<=x,j<=y,j>=x,j>=y} terms_tpl{j-x,j-y} @*/ j = 0;
 int /*@  predicates{i<=j,i<=x,i<=y,i>=j,i>=x,i>=y} terms_tpl{i-j,i-x,i-y} @*/ i = 0;


 while(unknown1())
 {
   x++;
   y++;
   i+=x;
   j+=y;
   if(flag)j+=1;
 }
 if(!(j>=i))
  errorFn();

}
