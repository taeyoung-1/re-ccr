#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include "xorlist.h"

//Performs the xor operation of two pointers
static intptr_t encrypt(node* prev, node* next) {
    return ((intptr_t) prev ^ (intptr_t) next);
}

static node* decrypt(intptr_t key, node* ptr) {
    return (node*) (key ^ (intptr_t) ptr);
}

//insertion takes place based on the 'at_tail' boolean value
void add(node** hd_handler, node** tl_handler, long item, bool at_tail) {

    node* entry = (node*) malloc(sizeof(node));
    node* hd = *hd_handler;
    node* tl = *tl_handler;
    entry->item = item;

    if (hd == NULL) {
        entry->link = 0;
        *hd_handler = *tl_handler = entry;
    } else if (at_tail) {
        entry->link = encrypt(tl, NULL);
        node* tl_prev = decrypt(tl->link, NULL);
        tl->link = encrypt(entry, tl_prev);
        *tl_handler = entry;
    } else {
        entry->link = encrypt(NULL, hd);
        node* hd_next = decrypt(hd->link, NULL);
        hd->link = encrypt(entry, hd_next);
        *hd_handler = entry;
    }
}

//deletion takes place based on the 'from_tail' boolean value
long delete(node** hd_handler, node** tl_handler, bool from_tail) {

    long item;

    if (NULL == hd_handler) {
        item = 0;
    } else if (from_tail) {
        // update tl_handler
        node* tl_old = *tl_handler;
        item = tl_old->item;
        node *tl_new = decrypt(tl_old->link, NULL);
        *tl_handler = tl_new;

        // update node information and free old tail
        if (tl_new == NULL) {
            *hd_handler = NULL;
        } else {
            node* tl_new_prev = decrypt(tl_new->link, tl_old);
            tl_new->link= encrypt(tl_new_prev, NULL);
        }
        free(tl_old);
    } else {
        // update hd_handler
        node* hd_old = *hd_handler;
        item = hd_old->item;
        node *hd_new = decrypt(hd_old->link, NULL);
        *hd_handler = hd_new;

        // update node information and free old head
        if (hd_new == NULL) {
            *tl_handler = NULL;
        } else {
            node* hd_new_next = decrypt(hd_new->link, hd_old);
            hd_new->link = encrypt(NULL, hd_new_next);
        } 
        free(hd_old);
    }
    return item;
}

// return ith element from handler. to_right determines the 0th index and searching direction
long search(node** hd_handler, node** tl_handler, bool from_tail, size_t index) {

    node* cur;
    node* prev = NULL;

    if (from_tail) {
        cur = *tl_handler;
    } else {
        cur = *hd_handler;
    }

    while (index--) {
        if (cur == NULL) {
            return 0;
        } else {
            node* next = decrypt(cur->link, prev);
            prev = cur;
            cur = next;
        }
    }

    return cur->item;
}