#include <stdio.h>

#include "xorlist.h"

void display(node* head) {
  node* curr = head;
  node* prev = NULL;
  long item;

  printf("\nList elements are : ");

  while (curr != NULL) {
    printf("%ld ", curr->item);
    node* next = (node*)((curr->link) ^ (intptr_t)prev);
    prev = curr;
    curr = next;
  }
  printf("\n\n");
}

int main(int argc, char* argv[]) {
  node *head = NULL, *tail = NULL;
  long item;

  for (long i = 0; i <= 9; i++) {
    if (i < 6) {
      add_hd(&head, &tail, i);
    } else {
      add_tl(&head, &tail, i);
    }
    printf("Successfully inserted %ld\n", i);
  }

  display(head);

  for (long i = 0; i <= 3; i++) {
    if (i < 2) {
      item = delete_hd(&head, &tail);
    } else {
      item = delete_tl(&head, &tail);
    }
    printf("Successfully deleted %ld\n", item);
  }

  display(head);
}