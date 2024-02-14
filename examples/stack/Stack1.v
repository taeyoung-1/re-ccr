Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import ProofMode.
Require Import Mem1.
Require Import AList.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Notation sget := (p0 <- trigger sGet;; `p0: (gmap mblock (list val)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation sput p0 := (trigger (sPut (p0: (gmap mblock (list val)))↑)) (only parsing).

  (* def new(): Ptr *)
  (*   let handle := Choose(Ptr); *)
  (*   guarantee(stk_mgr(handle) = None); *)
  (*   stk_mgr(handle) := Some []; *)
  (*   return handle *)

  Definition new_body: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;;
      handle <- trigger (Choose _);;;
      stk_mgr0 <- sget;;;
      guarantee(stk_mgr0 !! handle = None);;;
      let stk_mgr1 := <[handle:=[]]> stk_mgr0 in
      _ <- sput stk_mgr1;;;
      Ret (Vptr handle 0)
  .

  (* def pop(handle: Ptr): Int64 *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   match stk with *)
  (*   | x :: stk' =>  *)
  (*     stk_mgr(handle) := Some stk'; *)
  (*     return x *)
  (*   | [] => return -1 *)
  (*   end *)

  Definition pop_body: list val -> itree hEs val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;;
      stk_mgr0 <- sget;;;
      stk0 <- (stk_mgr0 !! handle)?;;;
      let stk_mgr1 := delete handle stk_mgr0 in _ <- sput stk_mgr1;;;
      match stk0 with
      | x :: stk1 =>
        stk_mgr2 <- sget;;; _ <- sput (<[handle:=stk1]> stk_mgr2);;;
        Ret x
      | _ =>
        stk_mgr2 <- sget;;; _ <- sput (<[handle:=[]]> stk_mgr2);;;
        Ret (Vint (- 1))
      end
  .

  (* def push(handle: Ptr, x: Int64): Unit *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   stk_mgr(handle) := Some (x :: stk); *)
  (*   () *)

  Definition push_body: list val -> itree hEs val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tuntyped] args)?;;;
      stk_mgr0 <- sget;;;
      stk0 <- (stk_mgr0 !! handle)?;;;
      let stk_mgr1 := delete handle stk_mgr0 in _ <- sput stk_mgr1;;;
      stk_mgr2 <- sget;; sput (<[handle:=(x :: stk0)]> stk_mgr2);;;
      Ret Vundef
  .

  Definition StackSbtb: list (gname * fspecbody) :=
    [("new", mk_specbody fspec_trivial (cfunU new_body));
    ("pop", mk_specbody fspec_trivial (cfunU pop_body));
    ("push", mk_specbody fspec_trivial (cfunU push_body))
    ].

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun fsb => fsb.(fsb_fspec): fspec)) StackSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition SStackSem: SModSem.t := {|
    SModSem.fnsems := StackSbtb;
    SModSem.initial_mr := ε;
    SModSem.initial_st := (∅: gmap mblock (list val))↑;
    (* SModSem.initial_st := tt↑; *)
  |}
  .
  Definition StackSem (stb: gname -> option fspec): ModSem.t :=
    (SModSem.to_tgt stb) SStackSem.



  Definition SStack: SMod.t := {|
    SMod.get_modsem := fun _ => SStackSem;
    SMod.sk := [("new", Gfun↑); ("pop", Gfun↑); ("push", Gfun↑)];
  |}
  .
  Definition Stack (stb: Sk.t -> gname -> option fspec): Mod.t :=
    (SMod.to_tgt stb) SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
