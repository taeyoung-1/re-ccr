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



Definition _stkRA: URA.t := (mblock ==> (Excl.t (list val)))%ra.
Instance stkRA: URA.t := Auth.t _stkRA.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Compute (URA.car (t:=_stkRA)).
  Definition _is_stack (h: mblock) (stk: list val): _stkRA :=
    (fun _h => if (dec _h h) then Some stk else ε)
  .

  Definition is_stack (h: mblock) (stk: list val): stkRA := Auth.white (_is_stack h stk).

  Definition new_spec: fspec :=
    (mk_simple (fun (_: unit) => (
                    (ord_pure 0),
                    (fun varg => (⌜varg = ([]: list val)↑⌝: iProp)%I),
                    (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** OwnM(is_stack h []): iProp)%I)
    )))
  .

  Definition pop_spec: fspec :=
    mk_simple (fun '(h, stk0) => (
                   (ord_pure 0),
                   (fun varg => (⌜varg = ([Vptr h 0%Z]: list val)↑⌝
                                   ** OwnM (is_stack h stk0): iProp)%I),
                   (fun vret =>
                      (match stk0 with
                       | [] => ⌜vret = (Vint (- 1))↑⌝ ** OwnM (is_stack h [])
                       | hd :: tl => ⌜vret = hd↑⌝ ** OwnM (is_stack h tl)
                       end: iProp)%I)
              ))
  .

  Definition push_spec: fspec :=
    mk_simple (fun '(h, x, stk0) => (
                   (ord_pure 0),
                   (fun varg => (⌜varg = ([Vptr h 0%Z; x]: list val)↑⌝
                                   ** OwnM (is_stack h stk0): iProp)%I),
                   (fun vret => (OwnM (is_stack h (x :: stk0)) ** ⌜vret = (Vundef)↑⌝: iProp)%I)
              ))
  .


  (*** TODO: remove redundancy with Stack2 ***)
  Notation sget := (p0 <- trigger sGet;; `p0: (gmap mblock (list val)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation sput p0 := (trigger (sPut (p0: (gmap mblock (list val)))↑)) (only parsing).



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

  Definition pop_body: list val -> itree hEs val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;;
      stk_mgr0 <- sget;;;
      stk0 <- (stk_mgr0 !! handle)?;;;
      match stk0 with
      | x :: stk1 =>
        _ <- sput (<[handle:=stk1]> stk_mgr0);;;
        Ret x
      | _ => Ret (Vint (- 1))
      end
  .

  Definition push_body: list val -> itree hEs val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tuntyped] args)?;;;
      stk_mgr0 <- sget;;;
      stk0 <- (stk_mgr0 !! handle)?;;;
      _ <- sput (<[handle:=(x :: stk0)]> stk_mgr0);;;
      Ret Vundef
  .


  Definition StackSbtb: list (gname * fspecbody) :=
    [("new", mk_specbody new_spec (cfunU new_body));
    ("pop",  mk_specbody pop_spec (cfunU pop_body));
    ("push", mk_specbody push_spec (cfunU push_body))
    ]
  .

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun fsb => fsb.(fsb_fspec): fspec)) StackSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition SStackSem: SModSem.t := {|
    SModSem.fnsems := StackSbtb;
    SModSem.initial_mr := GRA.embed (@Auth.black _stkRA ε);
    SModSem.initial_st := (∅: gmap mblock (list val))↑;
  |}
  .
  Definition StackSem (stb: gname -> option fspec): ModSem.t :=
    SModSem.to_tgt stb SStackSem.



  Definition SStack: SMod.t := {|
    SMod.get_modsem := fun _ => SStackSem;
    SMod.sk := [("new", Gfun↑); ("pop", Gfun↑); ("push", Gfun↑)];
  |}
  .
  Definition Stack (stb: Sk.t -> gname -> option fspec): Mod.t :=
    SMod.to_tgt stb SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
