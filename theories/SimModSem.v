Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.







Print function_Map. (*** TODO: use Dec. Move to proper place ***)

Global Instance Dec_RelDec K `{Dec K}: @RelDec K eq :=
  { rel_dec := dec }.

Global Instance Dec_RelDec_Correct K `{Dec K}: RelDec_Correct Dec_RelDec.
Proof.
  unfold Dec_RelDec. ss.
  econs. ii. ss. unfold Dec_RelDec. split; ii.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
Qed.









Module W.
Section WORLD.

  Context `{Σ: GRA.t}.

  Class t := {
    car: Type;
    le: car -> car -> Prop;
    wf: car -> Prop;
    le_PreOrder: PreOrder le;
    src: car -> alist mname Σ;
    tgt: car -> alist mname Σ;
  }
  .

End WORLD.
End W.






(* Section PLAYGROUND. *)
(*   Variable A B: Type. *)
(*   Variable left: A -> A -> Prop. *)
(*   Variable right: B -> B -> Prop. *)
(*   Inductive _sim (sim: nat -> A -> B -> Prop): nat -> A -> B -> Prop := *)
(*   | go_left *)
(*       i0 a0 b0 a1 *)
(*       i1 *)
(*       (*** can't choose i1 depending on a1 ***) *)
(*       (ORD: i1 < i0) *)
(*       (GO: left a0 a1) *)
(*       (K: sim i1 a1 b0) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_right *)
(*       i0 a0 b0 b1 *)
(*       i1 *)
(*       (ORD: i1 < i0) *)
(*       (GO: right b0 b1) *)
(*       (K: sim i1 a0 b1) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_both *)
(*       i0 a0 b0 i1 a1 b1 *)
(*       (GO: left a0 a1) *)
(*       (GO: right b0 b1) *)
(*       (K: sim i1 a1 b1) *)
(*     : *)
(*       _sim sim i0 a1 b1 *)
(*   . *)
(* End PLAYGROUND. *)
(* Reset PLAYGROUND. *)
(* (*** i1 can't depend on a1, or the internal choices inside "left" ***) *)


(* Section PLAYGROUND. *)
(*   Variable A B: Type. *)
(*   Variable left: nat -> A -> nat -> A -> Prop. *)
(*   Variable right: nat -> B -> nat -> B -> Prop. *)
(*   Variable both: (nat -> A -> B -> Prop) -> (nat -> A -> B -> Prop). *)
(*   Inductive _sim (sim: nat -> A -> B -> Prop): nat -> A -> B -> Prop := *)
(*   | go_left *)
(*       i0 a0 b0 a1 *)
(*       i1 *)
(*       (* (ORD: i1 < i0) *) *)
(*       (GO: left i0 a0 i1 a1) *)
(*       (K: sim i1 a1 b0) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_right *)
(*       i0 a0 b0 b1 *)
(*       i1 *)
(*       (* (ORD: i1 < i0) *) *)
(*       (GO: right i0 b0 i1 b1) *)
(*       (K: sim i1 a0 b1) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_left_right *)
(*       i0 a0 b0 _unused0_ _unused1_ i1 a1 b1 *)
(*       (GO: left i0 a0 _unused0_ a1) *)
(*       (GO: right i0 b0 _unused1_ b1) *)
(*       (K: sim i1 a1 b1) *)
(*     : *)
(*       _sim sim i0 a1 b1 *)
(*   | go_both *)
(*       i0 a0 b0 *)
(*       (GO: both sim i0 a0 b0) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   . *)

(*   Definition sim: _ -> _ -> _ -> Prop := paco3 _sim bot3. *)

(*   Lemma sim_mon (MON: monotone3 both): monotone3 _sim. *)
(*   Proof. *)
(*     ii. inv IN. *)
(*     - econs 1; eauto. *)
(*     - econs 2; eauto. *)
(*     - econs 3; eauto. *)
(*     - econs 4; eauto. *)
(*   Qed. *)

(* End PLAYGROUND. *)

(* Hint Constructors _sim. *)
(* Hint Unfold sim. *)
(* Hint Resolve sim_mon: paco. *)












Section SIM.

  Context `{Σ: GRA.t}.

  (* Let st_local: Type := (list (string * GRA) * GRA). *)
  Let st_local: Type := ((alist mname Σ) * Σ).

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Variable wf: W -> Prop.
  Variable le: relation W.
  Hypothesis le_PreOrder: PreOrder le.

  Variant _sim_itree (sim_itree: nat -> relation (st_local * (itree Es val)))
    : nat -> relation (st_local * (itree Es val)) :=
  | sim_itree_ret
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      (WF: wf (mrs_src0, mrs_tgt0))
      v
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), (Ret v)) ((mrs_tgt0, fr_tgt0), (Ret v))
  | sim_itree_tau
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_call
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (WF: wf (mrs_src0, mrs_tgt0))
      (K: forall vret mrs_src1 mrs_tgt1 (WF: wf (mrs_src1, mrs_tgt1)),
          exists i1, sim_itree i1 ((mrs_src1, fr_src0), k_src vret) ((mrs_tgt1, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Call fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Call fn varg) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)


  | sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_put_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 fr_src1
      (MR0: Maps.lookup mn mrs_src0 = Some mr0)
      (UPD: URA.updatable (URA.add mr0 fr_src0) (URA.add mr1 fr_src1))
      mrs_src1
      (EQ: mrs_src1 = Maps.add mn mr1 mrs_src0)
      (K: sim_itree i1 ((mrs_src1, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Put mn mr1 fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0
      (MR0: Maps.lookup mn mrs_src0 = Some mr0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src mr0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (MGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_fget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src fr_src0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_forge_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      delta
      (K: sim_itree i1 ((mrs_src0, URA.add fr_src0 delta), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Forge delta) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_discard_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      delta fr_src1
      (SPLIT: fr_src0 = URA.add fr_src1 delta)
      (K: sim_itree i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Discard delta) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_check_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0
      (MR0: Maps.lookup mn mrs_src0 = Some mr0)
      (K: forall (WF: (URA.wf (URA.add mr0 fr_src0))),
          sim_itree i1 ((mrs_src0, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (CheckWf mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_choose_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: i1 < i0)
      (K: exists (x: X), sim_itree i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Choose X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_take_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: i1 < i0)
      (K: forall (x: X), sim_itree i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Take X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)






  | sim_itree_tau_tgt
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_put_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 fr_tgt1
      (MR0: Maps.lookup mn mrs_tgt0 = Some mr0)
      (UPD: URA.updatable (URA.add mr0 fr_tgt0) (URA.add mr1 fr_tgt1))
      mrs_tgt1
      (EQ: mrs_tgt1 = Maps.add mn mr1 mrs_tgt0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Put mn mr1 fr_tgt1) >>= k_tgt)
  | sim_itree_mget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0
      (MR0: Maps.lookup mn mrs_tgt0 = Some mr0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mr0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MGet mn) >>= k_tgt)
  | sim_itree_fget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt  fr_tgt0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)
  (* | sim_itree_forge_src *)
  (*     i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0 *)
  (*     i1 k_src i_tgt *)
  (*     (ORD: i1 < i0) *)
  (*     delta *)
  (*     (K: sim_itree i1 ((mrs_src0, URA.add fr_src0 delta), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt)) *)
  (*   : *)
  (*     _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Forge delta) >>= k_src) *)
  (*                ((mrs_tgt0, fr_tgt0), i_tgt) *)
  (* | sim_itree_discard_src *)
  (*     i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0 *)
  (*     i1 k_src i_tgt *)
  (*     (ORD: i1 < i0) *)
  (*     delta fr_src1 *)
  (*     (SPLIT: fr_src0 = URA.add fr_src1 delta) *)
  (*     (K: sim_itree i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt)) *)
  (*   : *)
  (*     _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Discard delta) >>= k_src) *)
  (*                ((mrs_tgt0, fr_tgt0), i_tgt) *)
  (* | sim_itree_check_src *)
  (*     i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0 *)
  (*     i1 k_src i_tgt *)
  (*     (ORD: i1 < i0) *)
  (*     mn mr0 *)
  (*     (MR0: Maps.lookup mn mrs_src0 = Some mr0) *)
  (*     (K: forall (WF: (URA.wf (URA.add mr0 fr_src0))), *)
  (*         sim_itree i1 ((mrs_src0, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt)) *)
  (*   : *)
  (*     _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (CheckWf mn) >>= k_src) *)
  (*                ((mrs_tgt0, fr_tgt0), i_tgt) *)
  | sim_itree_choose_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: i1 < i0)
      (K: forall (x: X), sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: i1 < i0)
      (K: exists (x: X), sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Take X) >>= k_tgt)
  .

  Definition sim_itree: _ -> relation _ := paco3 _sim_itree bot3.

  Lemma sim_itree_mon: monotone3 _sim_itree.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree: paco.

  Definition sim_fsem: relation (list val -> itree Es val) :=
    (eq ==> (fun it_src it_tgt => forall mrs_src mrs_tgt (SIMMRS: wf (mrs_src, mrs_tgt)),
                 exists n, sim_itree n ((mrs_src, URA.unit), it_src)
                                     ((mrs_tgt, URA.unit), it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (list val -> itree Es val)) := RelProd eq sim_fsem.

End SIM.



(*** Q: do we need SimMemOh.le (and lepriv) ??? ***)

(*** Let's say that le/lepriv can be encoded using RA and CheckWf... ***)
(*** Q: Is "Source CheckWf >= Target CheckWf" trivial? or can be derived automatically? ***)
(*** A: I think no. It looks like a real user obligation. ***)
(*** N.B.: In the course of verifying "Source CheckWf >= Target CheckWf", one may need "le".
         For an instance, if target RA is in some sense monotonic, while source RA is unit,
         we have to prove that "Target CheckWf" holds from the ground. To do so, we need "le".
         I am not entirely sure that we don't need "lepriv",
         but (1) lepriv alone won't scale with concurrency,
         so we need separation (putting into/out of function local resource), then
         (2) it seems function-local resource (without lepriv) is sufficient for the cases
         that I can think of ***)

(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Variable (ms0 ms1: ModSem.t).

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Inductive sim: Prop := mk {
    wf: W -> Prop;
    le: W -> W -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf) ms0.(ModSem.fnsems) ms1.(ModSem.fnsems);
    sim_initial_mrs: wf (ms0.(ModSem.initial_mrs), ms1.(ModSem.initial_mrs));
  }.

End SIMMODSEM.

(*** TODO: SimMod, Mod for Mem0/Mem1 ***)





Require Import Mem0 Mem1 Hoare.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ} `{@GRA.inG (RA.excl Mem.t) Σ}.

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@RA.car Mem1._memRA).
  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists mem_src (mem_tgt: Mem.t),
        (<<SRC: mrs_src0 = Maps.add "mem" (GRA.padding (URA.black mem_src)) Maps.empty>>) /\
        (<<TGT: mrs_tgt0 = Maps.add "mem" (GRA.padding ((inl (Some mem_tgt)): URA.car (t:=RA.excl Mem.t)))
                                    Maps.empty>>) /\
        (<<SIM: inl (mem_tgt.(Mem.cnts)) = mem_src>>)
  .

  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Theorem correct: sim Mem1.mem Mem0.mem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. }
    econs; ss.
    - split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold Mem1.allocF, Mem0.allocF.
      Ltac go := try first[pfold; econs; [..|M]; (Mskip ss); et; check_safe; ii; left|
                           pfold; econsr; [..|M]; (Mskip ss); et; check_safe; ii; left].
      go. rename x into sz.
      unfold assume.
      Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r).
      igo.
      go. clarify. unfold HoareFun. go. rename x into rarg_src.
      unfold assume.
      igo.
      repeat go. clear_tac.
      Opaque URA.add.
      unfold unpadding, assume.
      igo.
      pfold. econsr; et. esplits; et.
      { ii. unfold GRA.padding. des_ifs. (*** TODO: should be trivial ***) }
      left.
      unfold unleftU. des_ifs; cycle 1.
      { exfalso. ss. unfold GRA.padding in Heq. des_ifs.
        admit "dependent type... use cast? lemma?".
        (* unfold PCM.GRA.cast_ra in *. *)
        (* unfold eq_rect_r, eq_rect, eq_sym in *. *)
        (* destruct (GRA.inG_prf). *)
        (* unfold eq_rect_r in *. ss. *)
        (* Set Printing All. *)
        (* erewrite rew_opp_l in Heq. *)
        (* unfold eq_rect_r in *. unfold eq_rect in *. unfold eq_sym in *. csc. *)
      }
      igo.
      assert(c = (Some mem_tgt)).
      { admit "dependent type". }
      clarify.
      unfold unwrapU. des_ifs. igo. des_ifs. unfold MPut. igo. repeat go.
      rename n into blk. rename z into ofs. rename mem_tgt into mem0. rename t into mem1.

      Ltac force_l := pfold; econs; [..|M]; Mskip ss; et.
      Ltac force_r := pfold; econsr; [..|M]; Mskip ss; et.

      force_l. exists (Vptr blk ofs). left.
      force_l.
      (* Eval compute in URA.car (t:=Mem1._memRA). *)
      (*** mret, fret ***)
      eexists (GRA.padding (URA.black ((inl (Mem.cnts mem1)): URA.car (t:=Mem1._memRA))),
               GRA.padding
                 (fold_left URA.add
                            (mapi (fun n _ => (blk, Z.of_nat n) |-> Vint 0)
                                  (repeat () sz)) URA.unit)). left.
      igo. force_l.
      {
        replace (fun k => URA.unit) with (URA.unit (t:=Σ)) by ss.
        rewrite URA.unit_idl.
        rewrite GRA.padding_add.
        rewrite <- URA.unit_id.
        apply URA.updatable_add; cycle 1.
        { apply URA.updatable_unit. }
        eapply GRA.padding_updatable.
        assert(sz = 1) by admit "let's consider only sz 1 case at the moment". subst.
        ss. clarify.
        clear - Heq1.
        replace (@URA.frag Mem1._memRA (@inr (forall _ _, option val) unit tt)) with
            (URA.unit (t:=Mem1.memRA)) by ss.
        rewrite URA.unit_idl.
        assert(ADD: (inl (Mem.cnts mem1)) =
                    URA.add (t:=Mem1._memRA) (inl (Mem.cnts mem0))
                            (inl (fun _b _ofs => if dec _b blk && dec _ofs 0%Z
                                                 then Some (Vint 0) else None))).
        { Local Transparent URA.add.

          Local Opaque RA.excl.
          ss.
          Local Transparent RA.excl.
          cbn.

          Set Printing All.


          Set Printing All.
          unfold Mem1._memRA. unfold URA.of_RA.
          ss. f_equal.
        }
        eapply URA.auth_alloc2.
        ss.
        replace (URA.frag (@inr (forall (_ : nat) (_ : Z), option val) unit tt)) with
            (URA.unit (t:=Mem1._memRA)).
        (inr ())
        fun k : nat => URA.unit) with (URA.unit (t:=Σ)) by ss.
        rewrite URA.unit_id.
        ii. ss. des_ifs.
        (* rewrite <- URA.unit_id with (a:=(URA.black ((inl (Mem.cnts mem0)): *)
        (*                                               URA.car (t:=Mem1._memRA)))). *)
        (* eapply URA.auth_update. *)
        ii. des.
        eapply URA.auth_alloc. ii. des. esplits; et.
        - ss. intros blk0 ofs0. admit "".
        -
        }
        eapply URA.auth_update.
        admit "use induction..".
      }
      left.
      ss.
      force_l. exists 

      go.
      ss.
      unfold unwrapU. des_ifs; cycle 1.
      { exfalso. ss. clarify. }
      repeat go.
      repeat go.
      pfold; econsr; [..|M]; Mskip ss; et. ss; et; ii; left.
      pfold. econs; ss; et; ii; left.
      repeat go.
      irw.
      repeat go.
      rewrite bind_bind.
      repeat go.

      pfold; econsr; et; ss.
      go.
      clarify.

      repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r).
      rewrite bind_trigger.
      rewrite bind_bind.
      ITree.bind'
      repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r).
    -
      go.
      des_ifs.
      go. go.
      clarify.
      
      pfold. econs; et.
  Qed.

End SIMMODSEM.


TODO: prove sim
TODO: write client
TODO: show cancellation
TODO: meta-level (no forge -> checkwf always succeeds)





















Section SIMMODSEM.

  Variable world: Type.
  Variable src: world -> GRA.
  Variable tgt: world -> GRA.

  Variable wf: world -> Prop.
  Variable le: world -> world -> Prop.
  Hypothesis le_PreOrder: PreOrder le.


  (* Variable idx: Type. *)
  (* Variable ord: idx -> idx -> Prop. *)
  (* Variable wf_ord: well_founded ord. *)

  (* Variable R: GRA -> GRA -> Prop. *)
  (* Variable R: list (string * (GRA -> GRA -> Prop)). *)
  (* Variable R: string -> option (GRA -> GRA -> Prop). *)
























  (* Let r_state := ModSem.r_state. *)
  (* Let handle_r := ModSem.handle_rE. *)
  (* Let interp_r := ModSem.interp_rE. *)

  (* Inductive _sim_fn sim_fn: nat -> (itree Es val * r_state) -> (itree Es val * r_state) -> Prop := *)
  (* | sim_fn_ret *)
  (*     i0 m_src0 m_tgt0 f_src0 f_tgt0 *)
  (*     (SIMM: R m_src0 m_tgt0) *)
  (*     v *)
  (*   : *)
  (*     _sim_fn sim_fn i0 ((Ret v), (m_src0, f_src0)) ((Ret v), (m_tgt0, f_tgt0)) *)
  (* | sim_fn_call *)
  (*     i0 m_src0 m_tgt0 f_src0 f_tgt0 *)
  (*     (SIMM: R m_src0 m_tgt0) *)
  (*     fn varg (i1: nat) k_src k_tgt *)
  (*     (K: forall rv m_src1 m_tgt1 (SIMM: R m_src1 m_tgt1), *)
  (*         sim_fn i1 (mk (k_src rv) f_src0 m_src1) (mk (k_src rv) f_tgt0 m_tgt1)) *)
  (*   : *)
  (*     _sim_fn sim_fn i0 (mk (trigger (Call fn varg) >>= k_src) f_src0 m_src0) *)
  (*             (mk (trigger (Call fn varg) >>= k_tgt) f_tgt0 m_tgt0) *)
  (* . *)
















  (* Variable R: string -> option (GRA -> GRA -> Prop). *)
  (* Hypothesis SIMMN: List.map fst ms0.(ModSem.initial_mrs) = List.map fst ms1.(ModSem.initial_mrs). *)
  (* Hypothesis RWF: forall mn, *)
  (*     is_some (R mn) -> is_some (List.find (dec mn) (List.map fst ms0.(ModSem.initial_mrs))). *)
  (* Definition RAll (m_src0 m_tgt0: list (string * GRA)): Prop := *)
  (*   Forall2 () m_src0 m_tgt0 *)
  (* . *)

  Variable R: relation (list (string * GRA)).

  (* Record st_local: Type := mk { *)
  (*   code: itree Es val; *)
  (*   fr: GRA; *)
  (*   (* mr: GRA; *) *)
  (*   mr: list (string * GRA); *)
  (* } *)
  (* . *)
  (* Let st_local: Type := (list (string * GRA) * GRA). *)

  Inductive _sim_fn sim_fn: nat -> sim_state -> sim_state -> Prop :=
  | sim_fn_ret
      i0 m_src0 m_tgt0 f_src0 f_tgt0
      (SIMM: R m_src0 m_tgt0)
      v
    :
      _sim_fn sim_fn i0 (mk (Ret v) f_src0 m_src0) (mk (Ret v) f_tgt0 m_tgt0)
  | sim_fn_call
      i0 m_src0 m_tgt0 f_src0 f_tgt0
      (SIMM: R m_src0 m_tgt0)
      fn varg (i1: nat) k_src k_tgt
      (K: forall rv m_src1 m_tgt1 (SIMM: R m_src1 m_tgt1),
          sim_fn i1 (mk (k_src rv) f_src0 m_src1) (mk (k_src rv) f_tgt0 m_tgt1))
    :
      _sim_fn sim_fn i0 (mk (trigger (Call fn varg) >>= k_src) f_src0 m_src0)
              (mk (trigger (Call fn varg) >>= k_tgt) f_tgt0 m_tgt0)
  | sim_fn_put_src
      i0 m_src0 m_tgt0 f_src0 f_tgt0
      (SIMM: R m_src0 m_tgt0)
      mn k_src c_tgt m_src1 f_src1
      i1
      (ORD: i1 < i0)
      (K: sim_fn i1 (nat 
    :
      _sim_fn sim_fn i0 (mk (trigger (Put mn m_src1 f_src1) >>= k_src) f_src0 m_src0)
              (mk (c_tgt) f_tgt0 m_tgt0)
  .
  callE
    rE
    ModSem.interp

  Definition sim_fn (fn_src fn_tgt: list val -> itree Es val): Prop.

End SIMMODSEM.



Module ModSem.
Section MODSEM.

  (* Record t: Type := mk { *)
  (*   state: Type; *)
  (*   local_data: Type; *)
  (*   step (skenv: SkEnv.t) (st0: state) (ev: option event) (st1: state): Prop; *)
  (*   state_sort: state -> sort; *)
  (*   initial_local_data: local_data; *)
  (*   sk: Sk.t; *)
  (*   name: string; *)
  (* } *)
  (* . *)

  Context `{GRA: GRA.t}.

  Record t: Type := mk {
    (* initial_ld: mname -> GRA; *)
    fnsems: list (fname * (list val -> itree Es val));
    initial_mrs: list (mname * GRA);
    sem: callE ~> itree Es :=
      fun _ '(Call fn args) =>
        '(_, sem) <- (List.find (fun fnsem => dec fn (fst fnsem)) fnsems)?;;
        sem args
  }
  .

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
    wf_initial_mrs: NoDup (List.map fst ms.(initial_mrs));
  }
  .

  (*** using "Program Definition" makes the definition uncompilable; why?? ***)
  Definition add (ms0 ms1: t): t := {|
    (* sk := Sk.add md0.(sk) md1.(sk); *)
    (* initial_ld := URA.add (t:=URA.pointwise _ _) md0.(initial_ld) md1.(initial_ld); *)
    (* sem := fun _ '(Call fn args) => *)
    (*          (if List.in_dec string_dec fn md0.(sk) then md0.(sem) else md1.(sem)) _ (Call fn args); *)
    fnsems := app ms0.(fnsems) ms1.(fnsems);
    initial_mrs := app ms0.(initial_mrs) ms1.(initial_mrs);
  |}
  .



  Section INTERP.

  Variable ms: t.

  Let itr0: callE ~> itree Es :=
    fun _ ce =>
      trigger PushFrame;;
      rv <- (ms.(sem) ce);;
      trigger PopFrame;;
      Ret rv
  .
  Let itr1: itree (rE +' eventE) val := (mrec itr0) _ (Call "main" nil).



  Definition r_state: Type := ((mname -> GRA) * list GRA).
  Definition handle_rE `{eventE -< E}: rE ~> stateT r_state (itree E) :=
    fun _ e '(mrs, frs) =>
      match frs with
      | hd :: tl =>
        match e with
        | Put mn mr fr =>
          guarantee(URA.updatable (URA.add (mrs mn) hd) (URA.add mr fr));;
          Ret (((update mrs mn mr), fr :: tl), tt)
        | MGet mn => Ret ((mrs, frs), mrs mn)
        | FGet => Ret ((mrs, frs), hd)
        | Forge fr => Ret ((mrs, (URA.add hd fr) :: tl), tt)
        | Discard fr =>
          rest <- trigger (Choose _);;
          guarantee(hd = URA.add fr rest);;
          Ret ((mrs, rest :: tl), tt)
        | CheckWf mn =>
          assume(URA.wf (URA.add (mrs mn) hd));;
          Ret ((mrs, frs), tt)
        | PushFrame =>
          Ret ((mrs, URA.unit :: frs), tt)
        | PopFrame =>
          Ret ((mrs, tl), tt)
        end
      | _ => triggerNB
      end.
  Definition interp_rE `{eventE -< E}: itree (rE +' E) ~> stateT r_state (itree E) :=
    State.interp_state (case_ handle_rE State.pure_state).
  Definition initial_r_state: r_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(initial_mrs) with
               | Some r => snd r
               | None => URA.unit
               end, []).
  Let itr2: itree (eventE) val := assume(<<WF: wf ms>>);; snd <$> (interp_rE itr1) initial_r_state.



  Let state: Type := itree eventE val.

  Definition state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv => final rv
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (Syscall fn args m0) k => vis
    end
  .

  Inductive step: state -> option event -> state -> Prop :=
  | step_tau
      itr
    :
      step (Tau itr) None itr
  | step_choose
      X k (x: X)
    :
      step (Vis (subevent _ (Choose X)) k) None (k x)
  | step_take
      X k (x: X)
    :
      step (Vis (subevent _ (Take X)) k) None (k x)
  | step_syscall
      fn args m0 k ev m1 rv
      (SYSCALL: syscall_sem fn args m0 = (ev, m1, rv))
    :
      step (Vis (subevent _ (Syscall fn args m0)) k) (Some ev) (k (m1, rv))
  .

  Program Definition interp: semantics := {|
    STS.state := state;
    STS.step := step;
    STS.initial_state := itr2;
    STS.state_sort := state_sort;
  |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. rewrite SYSCALL in *. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

  End INTERP.

  (*** TODO: probably we can make ModSem.t as an RA too. (together with Sk.t) ***)
  (*** However, I am not sure what would be the gain; and there might be universe problem. ***)

  Let add_comm_aux
      ms0 ms1 stl0 str0
      (SIM: stl0 = str0)
    :
      <<COMM: Beh.of_state (interp (add ms0 ms1)) stl0 <1= Beh.of_state (interp (add ms1 ms0)) str0>>
  .
  Proof.
    revert_until ms1.
    pcofix CIH. i. pfold.
    clarify.
    punfold PR. induction PR using Beh.of_state_ind; ss.
    - econs 1; et.
    - econs 2; et.
      clear CIH. clear_tac. revert_until ms1.
      pcofix CIH. i. punfold H0. pfold.
      inv H0.
      + econs 1; eauto. ii. ss. exploit STEP; et. i; des. right. eapply CIH; et. pclearbot. ss.
      + econs 2; eauto. des. esplits; eauto. right. eapply CIH; et. pclearbot. ss.
    - econs 4; et. pclearbot. right. eapply CIH; et.
    - econs 5; et. rr in STEP. des. rr. esplits; et.
    - econs 6; et. ii. exploit STEP; et. i; des. clarify.
  Qed.

  Lemma wf_comm
        ms0 ms1
    :
      <<EQ: wf (add ms0 ms1) = wf (add ms1 ms0)>>
  .
  Proof.
    r. eapply prop_ext. split; i.
    - admit "ez".
    - admit "ez".
  Qed.

  Theorem add_comm
          ms0 ms1
          (* (WF: wf (add ms0 ms1)) *)
    :
      <<COMM: Beh.of_program (interp (add ms0 ms1)) <1= Beh.of_program (interp (add ms1 ms0))>>
  .
  Proof.
    destruct (classic (wf (add ms1 ms0))); cycle 1.
    { ii. clear PR. eapply Beh.ub_top. pfold. econsr; ss; et. rr. ii; ss. unfold assume in *.
      inv STEP; ss; irw in H1; (* clarify <- TODO: BUG, runs infloop. *) inv H1; simpl_depind; subst.
      clarify.
    }
    rename H into WF.
    ii. ss. r in PR. r. eapply add_comm_aux; et.
    rp; et. clear PR. cbn. do 1 f_equal; cycle 1.
    { unfold assume. rewrite wf_comm. ss. }
    apply func_ext; ii.
    f_equiv.
    f_equal; cycle 1.
    - unfold initial_r_state. f_equal. apply func_ext. intros fn. ss. des_ifs.
      + admit "ez: wf".
      + admit "ez: wf".
      + admit "ez: wf".
    - repeat f_equal. apply func_ext_dep. intro T. apply func_ext. intro c. destruct c.
      repeat f_equal. apply func_ext. i. f_equal. ss. do 2 f_equal.
      admit "ez: wf".
  Qed.

  Theorem add_assoc
          ms0 ms1 ms2
          (WF: wf (add ms0 (add ms1 ms2)))
    :
      <<COMM: Beh.of_program (interp (add ms0 (add ms1 ms2))) <1=
              Beh.of_program (interp (add (add ms0 ms1) ms2))>>
  .
  Proof.
    admit "TODO".
  Qed.

  Theorem add_assoc_rev
          ms0 ms1 ms2
          (WF: wf (add ms0 (add ms1 ms2)))
    :
      <<COMM: Beh.of_program (interp (add ms0 (add ms1 ms2))) <1=
              Beh.of_program (interp (add (add ms0 ms1) ms2))>>
  .
  Proof.
    admit "TODO".
  Qed.

End MODSEM.
End ModSem.



Module Mod.
Section MOD.

  Context `{GRA: GRA.t}.

  Record t: Type := mk {
    get_modsem: SkEnv.t -> ModSem.t;
    sk: Sk.t;
    interp: semantics := ModSem.interp (get_modsem (Sk.load_skenv sk));
  }
  .

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  Definition wf (md: t): Prop := <<WF: Sk.wf md.(sk)>>.
  (*** wf about modsem is enforced in the semantics ***)

  Definition add (md0 md1: t): t := {|
    get_modsem := fun skenv_link =>
                    ModSem.add (md0.(get_modsem) skenv_link) (md1.(get_modsem) skenv_link);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .

  Theorem add_comm
          md0 md1
    :
      <<COMM: Beh.of_program (interp (add md0 md1)) <1= Beh.of_program (interp (add md1 md0))>>
  .
  Proof.
    ii.
    unfold interp in *. ss.
    eapply ModSem.add_comm; et.
    rp; et. do 4 f_equal.
    - admit "TODO: maybe the easy way is to 'canonicalize' the list by sorting.".
    - admit "TODO: maybe the easy way is to 'canonicalize' the list by sorting.".
  Qed.

  Theorem add_assoc
          md0 md1 md2
    :
      <<COMM: Beh.of_program (interp (add md0 (add md1 md2))) =
              Beh.of_program (interp (add (add md0 md1) md2))>>
  .
  Proof.
    admit "ez".
  Qed.

End MOD.
End Mod.


Module Equisatisfiability.
  Inductive pred: Type :=
  | true
  | false
  | meta (P: Prop)

  | disj: pred -> pred -> pred
  | conj: pred -> pred -> pred
  | neg: pred -> pred
  | impl: pred -> pred -> pred

  | univ (X: Type): (X -> pred) -> pred
  | exst (X: Type): (X -> pred) -> pred
  .

  (*** https://en.wikipedia.org/wiki/Negation_normal_form ***)
  Fixpoint embed (p: pred): itree eventE unit :=
    match p with
    | true => triggerUB
    | false => triggerNB
    | meta P => guarantee P

    | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 else embed p1
    | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 else embed p1
    | neg p =>
      match p with
      | meta P => assume P
      | _ => triggerNB (*** we are assuming negation normal form ***)
      end
    | impl _ _ => triggerNB (*** we are assuming negation normal form ***)

    | @univ X k => x <- trigger (Take X);; embed (k x)
    | @exst X k => x <- trigger (Choose X);; embed (k x)
    end
  .

  (*** TODO: implication --> function call? ***)
  (***
P -> Q
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q




(P -> Q) -> R
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q

pqrname :=
  (call pqname) (finite times);;
  embed R
   ***)

  (* Fixpoint embed (p: pred) (is_pos: bool): itree eventE unit := *)
  (*   match p with *)
  (*   | true => triggerUB *)
  (*   | false => triggerNB *)
  (*   | meta P => guarantee P *)
  (*   | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | @univ X k => x <- trigger (Take X);; embed (k x) is_pos *)
  (*   | @exst X k => x <- trigger (Choose X);; embed (k x) is_pos *)
  (*   | _ => triggerNB *)
  (*   end *)
  (* . *)
End Equisatisfiability.
