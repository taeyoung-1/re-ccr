#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "xorlist.h"

//Performs the xor operation of two pointers
intptr_t encrypt(node *a, node *b)
{
    return ((intptr_t) a ^ (intptr_t) b);
}
intptr_t decrypt(intptr_t xored, node *ptr)
{
  return (xored ^ (intptr_t) ptr);
}

//insertion takes place based on the 'at_tail' boolean value
void insert(node **head, node **tail, long item, bool at_tail)
{
    node *ptr = (node*) malloc(sizeof(node));
    ptr->item = item;

    if (NULL == *head) {
        ptr->link = 0;
        *head = *tail = ptr;
    } else if (at_tail) {
        ptr->link = encrypt(*tail, NULL);
        (*tail)->link = encrypt(ptr, (node *) decrypt((*tail)->link, NULL));
        *tail = ptr;
    } else {
        ptr->link = encrypt(NULL, *head);
        (*head)->link = encrypt(ptr, (node *) decrypt((*head)->link, NULL));
        *head = ptr;
    }
}

//deletion takes place from the end
long delete(node **head, node **tail, bool from_tail)
{
    long item;
    node *ptr;
    if (NULL == head) {
        return 0;
    } else if (from_tail) {
        ptr = *tail;
        item = ptr->item;
        node *prev = (node *) decrypt(ptr->link, NULL);
        if (NULL == prev) *head = NULL;
        else prev->link= encrypt(ptr, (node *) decrypt(prev->link, NULL));
        *tail = prev;

    } else {
        ptr = *head;
        item = ptr->item;
        node *next = (node *) decrypt(ptr->link, NULL);
        if (NULL == next) *tail = NULL;
        else next->link = encrypt(ptr, (node *) decrypt(next->link, NULL));
        *head = next;
    }
    free(ptr);
    ptr = NULL;
    return item;
}