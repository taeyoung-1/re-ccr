Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Mem1 MemOpen.
Require Import EchoHeader.
Require Import IPM HoareDef OpenDef.
Require Import Stack3A.

Set Implicit Arguments.




Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Definition echo_body: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;;
      `stk0: list Z    <- (ccallN "input" ([]: list Z));;;
      `_: list Z    <- (ccallN "output" (stk0));;;
      Ret Vundef
  .




  Let is_int_stack (h: mblock) (stk0: list Z): iProp :=
    (OwnM (is_stack h (List.map Vint stk0)) ∧ ⌜Forall (fun z => (z <> (- 1)%Z) /\ (intrange_64 z)) stk0⌝)%I
  .

  Definition input_spec: fspec :=
    mk_fspec (fun _ => ord_top)
             (fun h _argh _argl =>
                (∃ (stk0: list Z) (argl: list val),
                  ⌜_argh = stk0↑ ∧ _argl = argl↑ ∧ argl = [Vptr h 0]⌝
                   ** (is_int_stack h stk0))%I)
             (fun h _reth _retl => (∃ (stk1: list Z), ⌜_reth = stk1↑ ∧ _retl = Vundef↑⌝ ** is_int_stack h stk1)%I)
  .

  Definition input_body: list Z -> itree hEs (list Z) :=
    fun stk =>
      n <- (ccallU "getint" ([]: list val));;;
      assume(wf_val n);;;
      n <- (parg Tint n)?;;;
      if (dec n (- 1)%Z)
      then Ret stk
      else
        ret <- (ccallN "input" (n :: stk));;; Ret ret
  .





  Definition output_spec: fspec :=
    mk_fspec (fun _ => ord_top)
             (fun h _argh _argl =>
                (∃ (stk0: list Z) (argl: list val),
                  ⌜_argh = stk0↑ ∧ _argl = argl↑ ∧ argl = [Vptr h 0]⌝
                   ** is_int_stack h stk0)%I)
             (fun h _reth _retl => (∃ (stk1: list Z), ⌜_reth = stk1↑ ∧ _retl = Vundef↑⌝ ** is_int_stack h stk1)%I)
  .

  Definition output_body: list Z -> itree hEs (list Z) :=
    fun stk =>
      ;;;
      match stk with
      | [] => Ret []
      | n :: stk' =>
        `_: val <- (ccallU "putint" ([Vint n]: list val));;;
         ret <- (ccallN "output" (stk'));;;
         Ret ret
      end
  .





  Definition EchoSbtb: list (gname * fspecbody) :=
    [("echo", mk_specbody fspec_trivial (cfunU echo_body));
    ("input",  mk_specbody input_spec (cfunN input_body));
    ("output", mk_specbody output_spec (cfunN output_body))
    ]
  .

  Definition EchoStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun fsb => fsb.(fsb_fspec): fspec)) EchoSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition SEchoSem: SModSem.t := {|
    SModSem.fnsems := EchoSbtb;
    SModSem.initial_mr := ε;
    SModSem.initial_st := (∅: gmap mblock (list Z))↑;
  |}
  .
  Definition EchoSem (stb: gname -> option fspec): ModSem.t :=
    SModSem.to_tgt stb SEchoSem.



  Definition SEcho: SMod.t := {|
    SMod.get_modsem := fun _ => SEchoSem;
    SMod.sk := [("echo", Gfun↑); ("input", Gfun↑); ("output", Gfun↑)];
  |}
  .
  Definition Echo (stb: Sk.t -> gname -> option fspec): Mod.t :=
    SMod.to_tgt stb SEcho.

End PROOF.
Global Hint Unfold EchoStb: stb.
