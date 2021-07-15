struct node
{
  struct node *L;
  struct node *R;
};

void main()
{
  /* initialize the doubly linked list with a single node  */
  struct node* list=malloc(sizeof(struct node));
  list->L=0;
  list->R=0;
  struct node *tail=list;

  /* initialize a node and add to the tail of the list */
  struct node *n=malloc(sizeof(struct node)); 
  n->L=tail;
  n->R=0;
  tail->R=n;
  tail=n;

  /* now the list should have two elements */
  assert(list != tail);
}
