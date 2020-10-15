struct parent;
struct child;

struct child {
  struct parent *p;
  int data;
};

struct parent {
  struct child *child1, *child2;
};

void main()
{
  struct parent* list = calloc(sizeof(struct parent));
  list->child1 = calloc(sizeof(struct child));
  list->child1->p = list;
  list->child2 = calloc(sizeof(struct child));
  list->child2->p = list;

  struct parent *cp1 = list->child1->p; //commenting out this line
                                        //removes the assertion error
  struct parent *cp2 = list->child2->p;
  assert(list->child1->p == list); //should succeed after refinements
}
