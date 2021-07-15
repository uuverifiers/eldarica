typedef enum {false, true} _Bool;

_Bool nondet_bool(void);

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

  /* conditionally initialize a node and add to the tail of the list */
  if(nondet_bool()){
    struct node *n=malloc(sizeof(struct node)); 
    n->L=tail;
    n->R=0;
    tail->R=n;
    tail=n;
  }

  /* this assertion should fail, maybe no nodes were added */
  assert(list != tail);
}
