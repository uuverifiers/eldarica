extern int n;
void main() {
	int x,y;
 	assume(x==n&&y==n&&n>=0);
	while(x!=0){
		x--;
		y--;
	}
	assert(y==0);
}


