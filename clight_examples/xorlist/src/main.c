#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "xorlist.h"

extern void add(node**, node**, long, bool);

extern int delete(node**, node**, bool);

extern long search(node**, node**, bool, size_t);

void display(node *head, bool test)
{
    node *curr = head;
    node *prev = NULL, *next;
    int limit = test?6:10;
    long item;

    printf("\nList elements are : ");
    for (int i = 0; i < limit; i++) {
        item = search(&head, NULL, false, i);
        printf("%ld ", item);
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

    display(head, false);
    printf("\n");
    for (long i = 1; i <= 4; i++){
        item=delete(&head, &tail, i < 3);
        printf("Successfully deleted %ld\n",item);
    }

    display(head, true);
}