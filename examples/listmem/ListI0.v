Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import Imp.

Require Import lmHeader.

Set Implicit Arguments.

(***
struct node 
{
  int key;
  void* value;
  struct node *nextptr;
}

struct node **new_list()
{
  struct node **header = c_malloc(sizeof(struct node * ));
  *header = NULL;
  return header;
}

void insert_node(struct node **head, int node_key, void* node_value)
{
  struct node *new_node = c_malloc(sizeof(struct node));

  new_node->key = node_key;
  new_node->value = node_value;
  new_node->nextptr = *head;
  *head = new_node;
}

void *find_and_remove_node(struct node **head, int node_key)
{
  void *ret_val;
  struct node **prev_nextptr = head;
  struct ndoe *curr_node = *head;
  while (curr_node != NULL)
  {
    if (curr_node->key == node_key)
    {
      break;
    }
    prev_nextptr = &(curr_node->nextptr);
    curr_node = curr_node->nextptr;
  }

  ret_val = curr_node ? curr_node->value : NULL;

  if (curr_node != NULL)
  {
    *prev_nextptr = curr_node->nextptr;
    c_free(curr_node);
  }

  return ret_val;
}


--------------------

sizeof(node) = 
sizeof(node * ) =  

***)

Section L.
  Local Open Scope string_scope.

  Definition new_list: list val -> itree Es val :=
    fun varg =>
      `hptr:val <- ccallU "c_malloc" [Vint 8];;
      `_:val <- ccallU "store" [hptr;Vnullptr];;
      Ret hptr
  .

  Definition insert_node: list val -> itree Es val :=
    fun varg =>
      '(h, (k, v)) <- (pargs [Tuntyped; Tuntyped; Tuntyped] varg)?;;
      `node : val <- ccallU "c_malloc" [Vint 24];;
      `head : val <- ccallU "load" [h];;    

      node_val <- (vadd node (Vint 8))?;;
      node_next <- (vadd node (Vint 16))?;;

      `_ : val <- ccallU "store" [node; k];; (* Vptr (blk, off), key*)
      `_ : val <- ccallU "store" [node_val; v];;
      `_ : val <- ccallU "store" [node_next; head];;

      `_ : val <- ccallU "store" [h; node];;
      (* `_: val <- ccallU "scan" [h];; *)
      Ret Vundef
  .
      
  Definition find_and_remove_node: list val -> itree Es val :=
    fun varg =>
      '(head, nkey) <- (pargs [Tuntyped; Tuntyped] varg)?;;
      let prev_nextptr := head in
      `curr_node:val <- ccallU "load" [head];;
      
      (**)
      '(curr_node, prev_nextptr) <- (ITree.iter
              (fun i =>
                let '(curr_node, prev_nextptr) := i in
                `b1 : val <- ccallU "cmp" [curr_node;Vnullptr];;
                assume((wf_val b1) /\ (match b1 with | Vint _ => True | _ => False end));;;
                if dec (Vint 0) b1
                then (
                  ckey <- ccallU "load" [curr_node];;
                  `b2 : val <- ccallU "cmp" [ckey; nkey];;
                  assume((wf_val b2) /\ (match b2 with | Vint _ => True | _ => False end));;;
                  if dec (Vint 0) b2
                  then (
                    (*
                    _ <- printV ckey;;
                    _ <- printV nkey;;
                    _ <- printV curr_node;;
                    *)
                    prev_nextptr <- (vadd curr_node (Vint 16))?;;
                    `curr_node:val <- ccallU "load" [prev_nextptr];;
                    (*
                    _ <- printV prev_nextptr;;
                    _ <- printV curr_node;;
                    *)

                    Ret (inl (curr_node, prev_nextptr))
                    )
                    else (
                      (* break *)
                      
                      Ret (inr (curr_node, prev_nextptr))
                  )
                )
                else (
                  (* while loop end *)
                  Ret (inr (curr_node, prev_nextptr))
                )
      ) (curr_node, prev_nextptr));;
      
              
      `b2 : val <- ccallU "cmp" [curr_node;Vnullptr];;
      (**)

      ret_val <- (if dec (Vint 0) b2
      then (
        (**)
        vptr <- (vadd curr_node (Vint 8))?;; 
        `r:val <- ccallU "load" [vptr];;

        `curr_next_ptr:val <- (vadd curr_node (Vint 16))?;;
        `next : val <- ccallU "load" [curr_next_ptr];;
        
        `_:val <- ccallU "store" [prev_nextptr; next];;
        `_:val <- ccallU "c_free" [curr_node];;

               
        Ret r
      )
      else (
        Ret Vnullptr
      ));;
      
      (**)

      Ret ret_val
      .
    Definition ScanAll : list val -> itree Es val :=
      fun varg =>
      hd <- (pargs [Tuntyped] varg)?;;
      _ <- printV hd;;
      `curr:val <- ccallU "load" [hd];;
      _ <- (ITree.iter 
            ( fun i =>
              let curr := i in
              `b:val <- ccallU "cmp" [curr;Vnullptr];;
              assume((wf_val b) /\ (match b with | Vint _ => True | _ => False end));;;
              if dec (Vint 0) b (* not null *)
              then (
                _ <- printV (Vint 6);;  
                _ <- printV curr;; (* current node *)

                `sz: val <- ccallU "load" [curr];;
                _ <- printV sz;; (* key: curr[0] *)
                
                vp <- (vadd curr (Vint 8))?;;
                `v: val <- ccallU "load" [vp];;
                _ <- printV v;; (* value: curr[1] *)
                
                np <- (vadd curr (Vint 16))?;;
                `next:val <- ccallU "load" [np];;
                _ <- printV next;; (* next: curr[2]*)

                _ <- printV (Vint 9);;

                Ret (inl next)
              )
              else (
                Ret (inr Vnullptr)
              )

      ) curr);;
      Ret Vundef
  .
    Definition ListSem : ModSem.t := {|
      ModSem.fnsems := [("scan", cfunU ScanAll); ("new_list", cfunU new_list); ("insert_node", cfunU insert_node); ("find_and_remove_node", cfunU find_and_remove_node)];
      ModSem.init_st := Vundef↑;
    |}
  .
    
    Definition List: Mod.t := {|
      Mod.get_modsem := fun _ => ListSem;
      Mod.sk := [("scan", Gfun↑); ("new_list", Gfun↑); ("insert_node", Gfun↑); ("find_and_remove_node", Gfun↑)];
    |}
  .
                    
End L.