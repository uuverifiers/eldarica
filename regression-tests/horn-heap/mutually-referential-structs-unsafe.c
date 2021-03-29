struct parent;
struct child;

struct child {
  struct parent *p;
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
  //list->child2->p = list;

  assert(list->child1->p == list->child2->p);
}
