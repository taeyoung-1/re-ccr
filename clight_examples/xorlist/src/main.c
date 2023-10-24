#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "xorlist.h"

extern void add(node **head, node **tail, long item, bool at_tail);

extern int delete(node **head, node **tail, bool from_tail);

extern node* search(node *left, node *right, bool to_right, size_t index);

void display(node *head)
{
    node *curr = head;
    node *prev = NULL, *next;

    printf("\nList elements are : ");
    while (curr != NULL) {
        printf("%ld ", curr->item);
        next = search(prev, curr, true, 1);
        prev = curr;
        curr = next;
    }

    printf("\n");
}

int main(int argc, char *argv[])
{
    node *head = NULL, *tail = NULL;
    long item;
    for (long i = 1; i <= 10; i++){
        add(&head, &tail, i, i < 6);
        printf("Successfully inserted %ld\n",i);
    }

    display(head);
    printf("\n");
    for (long i = 1; i <= 4; i++){
        item=delete(&head, &tail, i < 3);
        printf("Successfully deleted %ld\n",item);
    }

    display(head);
}