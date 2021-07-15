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

int main()
{
 int /*@  predicates{i==1} predicates_tpl{0==0} @*/ i = 1;
 int /*@  predicates{j==0} @*/ j = 0;
 int z = i-j;
 int /*@  predicates{x<=z,x>=z} terms_tpl{x-z} @*/ x = 0;
 int /*@  predicates{y<=x,y<=z,y>=x,y>=z} terms_tpl{y-x,y-z} @*/ y = 0;
 int /*@  predicates{w<=x,w<=y,w<=z,w>=x,w>=y,w>=z} terms_tpl{w-2*x,w-2*y,w-z} @*/ w = 0;

 while(unknown2())
 {
  z+=x+y+w;
  y++;
  if(z%2==1)
    x++;
  w+=2;
 }

 if(!(x==y))
  errorFn();
}
