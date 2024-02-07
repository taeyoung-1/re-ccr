Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.

Set Implicit Arguments.

(***

Goal: get rid of c-dependent things

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
      let header := Vnullptr in
      `_:val <- ccallU "store" [hptr;header];;
      Ret hptr
  .

  Definition insert_node: list val -> itree Es val :=
    fun varg =>
      '(h, k, v) <- (pargs [Tptr; Tint; Tptr] varg)?;;
      `node : val <- ccallU "c_malloc" [Vint 24];;
      `head : val <- ccallU "load" [h];;
      let key := k in
      let value := v in
      let nextptr := head in
      `_ : val <- ccallU "store" [node;(Vint key)];;
      `_ : val <- ccallU "store" [(vadd node (Vint 8)); value];;
      `_ : val <- ccallU "store" [(vadd node (Vint 16)); nextptr];;
      `_ : val <- ccallU "store" [h;node];;
      Ret Vundef
  .


  Definition find_and_remove_node: list val -> itree Es val :=
    fun varg =>
      '(head, nkey) <- (pargs [Tptr; Tint] varg)?;;
      let prev_nextptr := head in
      `curr_node <- ccallU "load" [head];;
      pput curr_node;;;
      _ <- (ITree.iter
              (fun i =>
                `b : val <- ccallU "cmp" [curr_node;Vnullptr];;
                assume(wf_val b) /\ (match b with | Vint _ => True | _ => False end);;;
                if dec (Vint 0) b
                then (
                  `ckey : Z <- ccallU "load" [curr_node];;
                  if dec ckey nkey
                  then (
                    (* break *)
                    Ret
                  )
                  else (
                    prev_nextptr <- vadd curr_node (Vint 16);;
                    curr_node <- ccallU "load" [prev_nextptr];;
                    Ret
                  )
                )
                else (
                  (* while loop end *)
                  Ret
                )
              ) 0%Z );;
      `b2 : val <- ccallU "cmp" [curr_node;Vnullptr];;
      if dec (Vint 0) b2
      then (
        ret_val <- ccallU "load" [(vadd curr_node (Vint 8))];;
        `p : val <- ccallU "load" [(vadd curr_node (Vint 16))];;
        _ <- ccallU "store" [prev_nextptr; p];;
        _ <- ccallU "c_free" [curr_node];;
        Ret ret_val
      )
      else (
        Ret Vnullptr
      )
      .
      
      

  Definition ListSem : ModSem.t := {|
    ModSem.fnsems := [("new_list", cfunU new_list); ("insert_node", cfunU insert_node); ("find_and_remove_node", cfunU find_and_remove_node)];
    ModSem.mn := "List";
    ModSem.initial_st := Vnullptr;
  |}
  .

  Definition List: Mod.t := {|
    Mod.get_modsem := fun _ => ListSem;
    Mod.sk := [("new_list", Gfun↑); ("insert_node", Gfun↑); ("find_and_remove_node", Gfun↑)];
  |}
  .
                
