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

#define OFFSET sizeof(int)
void *memory = NULL;
struct node **freelist = NULL;
void *current_mem = NULL;
int current_size = 0;

void mem_init()
{
  memory = malloc(0x1000);
  current_mem = memory;
  current_size = 0x1000;
  freelist = new_list();
}

void *c_malloc(int size)
{
  if (size <= 0)
    return NULL;

  int real_size = size + OFFSET;
  void *chunk = NULL;

  if (freelist != NULL)
    chunk = find_and_remove_node(freelist, real_size);

  if (chunk != NULL)
    printf(chunk, real_size);
  else
    if (current_size >= real_size)
    {
      chunk = current_mem;
      current_mem += real_size;
      current_size -= real_size;
      printf;
    }
    else
      out_of_memory;
    
  if (chunk != NULL)
    * (int * ) chunk = real_size;
  
  return chunk + OFFSET
}

void c_free(void* ptr)
{
  ptr = ptr - OFFSET;
  insert_node(freelist, *(int * ) ptr, ptr);
}

void mem_clear()
{
  free(memory);
  memory = NULL;
  freelist = NULL;
  current_mem = NULL;
  current_size = 0;
}

-----------
OFFSET(sizeof(int)) = 


***)

Section M.
  Local Open Scope string_scope.

  Definition init: list val -> itree Es val :=
    fun varg =>
      sz <- (pargs [Tuntyped] varg)?;;
      `_:val <- ccallU "mem_init" [sz];;
      `_: val <- ccallU "fl_init" (@nil val);;
    Ret Vundef
  .

  Definition mem_init: list val -> itree Es val :=
    fun varg =>
      `mem_size: Z <- (pargs [Tint] varg)?;;
      `memory: val <- ccallU "alloc" [(Vint mem_size)];;
      _ <- (ITree.iter
              (fun i =>
                 if (Z_lt_le_dec i mem_size)
                 then
                   vptr <- (vadd memory (Vint (i * 8)))?;;
                   `_: val <- ccallU "store" [vptr; Vnullptr];;
                   Ret (inl (i + 1)%Z)
                 else
                   Ret (inr tt)) 0%Z);;
      trigger (sPut (memory, memory, memory, (Vint mem_size))↑);;; 
      (* memory, curr_mem, freelist, curr_size*)
      Ret Vundef
  .

  Definition fl_init: list val -> itree Es val :=
      fun varg =>
      `freelist:val <- ccallU "new_list" (@nil val);;
      data <- trigger sGet;;
      `data: (val*val*val*val) <- data↓?;;
      let '(memory, curr_mem, _, curr_size) := data in
      trigger (sPut (memory, curr_mem, freelist, curr_size)↑);;; 
      Ret Vundef
    .


  Definition c_malloc: list val -> itree Es val :=
    fun varg =>
      size <- (pargs [Tuntyped] varg)?;;
      `real_size: val <- (vadd size (Vint 8))?;; (* 1 or 8 *)
      data <- trigger sGet;;
      `data: (val*val*val*val) <- data↓?;;
      let '(memory, curr_mem, freelist, curr_size) := data in
   
      _ <- printVint [curr_size];; 

      `fl:val <- ccallU "load" [freelist];;
      `b1: val <- (ccallU "cmp" [fl; Vnullptr]);;
      assume((wf_val b1) /\ (match b1 with | Vint _ => True | _ => False end));;;
      chunk <- (if dec (Vint 0) b1
        then (ccallU "find_and_remove_node" [freelist;real_size])
        else Ret Vnullptr
      );;

      `b2: val <- (ccallU "cmp" [chunk; Vnullptr]);;
      assume((wf_val b2) /\ (match b2 with | Vint _ => True | _ => False end));;;
      
      r <- (if dec (Vint 0) b2
        then (
          (* chunk found in freelist *)
          (* _ <- trigger (Syscall "print" [(Z.of_nat 1)]↑ top1) ;;*)
          (* `v:val <- (vadd chunk (Vint 8))?;; *)
          (* trigger (PPut (memory, curr_mem, freelist, curr_size)↑);;; *)
          Ret chunk
        )
        else (
          `rz: Z <- (unint real_size)?;;
          `cz: Z <- (unint curr_size)?;; 

          if Z_le_gt_dec rz cz
          then (
            (* Allocating new memory chunk *)
            let chunk := curr_mem in
            `_: val <- ccallU "store" [chunk; real_size];;
            `v:val <- (vadd chunk (Vint 8))?;;
            curr_mem <- (vadd curr_mem real_size)?;;
            curr_size <- (vsub curr_size real_size)?;;
            trigger (sPut (memory, curr_mem, freelist, curr_size)↑);;; 
            
            Ret v
          )
          else (
            _ <- trigger (Syscall "print" [(Z.of_nat 2)]↑ top1) ;;
            (* trigger (PPut (memory, curr_mem, freelist, curr_size)↑);;; *)
            Ret Vnullptr
          )
        )
      ) ;;
            
      Ret r
  .   

  Definition c_free: list val -> itree Es val :=
    fun varg =>
      ptr <- (pargs [Tuntyped] varg)?;;
      fptr <- (vsub ptr (Vint 8))?;;
      data <- trigger sGet;;
      `data: (val*val*val*val) <- data↓?;;
      let '(memory, curr_mem, freelist, curr_size) := data in
      `sz : val <- ccallU "load" [fptr];; (* size of returned memory block *)
      `_ : val <- ccallU "insert_node" [freelist; sz; ptr];;
      
      Ret Vundef
  .

  Definition mem_clear : list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      data <- trigger sGet;;
      `data: (val*val*val*val) <- data↓?;;
      let '(memory, curr_mem, freelist, curr_size) := data in
      
      `_ : val <- ccallU "scan" [freelist];; (* view freelist before reset *)
      
      `_ : val <- ccallU "free" [memory];; (* physical free *)
      trigger (sPut (Vnullptr, Vnullptr, Vnullptr, Vnullptr)↑);;; (* initial state *)
      Ret Vundef
  .


  Definition main: list val -> itree Es val :=
      fun varg =>
        _ <- init [(Vint 512)];;
        node1 <- c_malloc [(Vint 64)];;
        node2 <- c_malloc [(Vint 80)];;
        node3 <- c_malloc [(Vint 80)];;
        (*
        _ <- printV node1;;
        _ <- printV node2;;
        _ <- printV node3;;
        *)
        _ <- c_free[node1];;
        _ <- c_free[node2];;
        _ <- c_free[node3];;


        n1 <- c_malloc [(Vint 80)];;
        n2 <- c_malloc [(Vint 80)];;
        n3 <- c_malloc [(Vint 48)];;
        n4 <- c_malloc [(Vint 64)];;
        n5 <- c_malloc [(Vint 48)];;

        (*
        _ <- c_free [n3];;
        _ <- c_free [n5];;
        *)

        (*
        _ <- printV n1;;
        _ <- printV n2;;
        _ <- printV n4;;
*)
        _ <- mem_clear [];;
        Ret Vundef
  .

  Definition cMemSem : ModSem.t := {|
    ModSem.fnsems := [("init", cfunU init); ("fl_init", cfunU fl_init); ("mem_init", cfunU mem_init); ("c_malloc", cfunU c_malloc); ("c_free", cfunU c_free); ("mem_clear", cfunU mem_clear); ("mainx", cfunU main)];
    ModSem.init_st := (Vnullptr, Vnullptr, Vnullptr, Vnullptr)↑; 
  |}
  .

  Definition cMem : Mod.t := {|
    Mod.get_modsem := fun _ => cMemSem;
    Mod.sk := [("init", Sk.Gfun); ("fl_init", Sk.Gfun); ("mem_init", Sk.Gfun); ("c_malloc", Sk.Gfun); ("c_free", Sk.Gfun); ("mem_clear", Sk.Gfun); ("mainx", Sk.Gfun)];
  |}
  .

  End M.



   (****
    

  ****)