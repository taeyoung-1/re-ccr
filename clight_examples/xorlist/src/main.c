#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "xorlist.h"


extern intptr_t decrypt(intptr_t a, node *b);

extern void insert(node **head, node **tail, long item, bool at_tail);

extern int delete(node **head, node **tail, bool from_tail);

void display(node *head)
{
    node *curr = head;
    node *prev = NULL, *next;

    printf("\nList elements are : ");
    while (NULL != curr) {
        printf("%ld ", curr->item);
        next = (node *) decrypt(curr->link, prev);
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
        insert(&head, &tail, i, i < 6);
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