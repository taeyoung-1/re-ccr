Require Import Coqlib.
Require Import String.
Require Import ITreelib.
(* Require Import Qcanon. *)
(* (*** from stdpp ***) *)
(* Record Qp : Set := mk_Qp { Qp_car : Qc;  Qp_prf : 0 < Qp_car }. *)

Set Implicit Arguments.



Definition cast A B (LeibEq: A = B) (a: A): B := eq_rect A _ a _ LeibEq.

(* Class LeibEq (A B: Type) := { leibeq: A = B }. *)
(* Arguments LeibEq: clear implicits. *)
(* Program Definition LeibEq_rev (A B: Type) (LEQ: LeibEq A B): LeibEq B A. *)
(* Proof. rewrite leibeq. econstructor. refl. Defined. *)
(* Definition cast (A B: Type) `{LeibEq A B} (a: A): B. rewrite <- leibeq. apply a. Defined. *)
(* Global Program Instance LeibEq_refl (A: Type): LeibEq A A. *)

(* Lemma cast_elim *)
(*       A LEQ (a: A) *)
(*   : *)
(*     <<EQ: (@cast A A LEQ a) = a>> *)
(* . *)
(* Proof. *)
(*   r. destruct LEQ. *)
(*   unfold cast. ss. *)
(*   unfold eq_rect. dependent destruction leibeq0. ss. *)
(* Qed. *)

(* Lemma unit_JMeq *)
(*       X (x: X) *)
(*       (TY: X = unit) *)
(*   : *)
(*     <<EQ: x ~= tt>> *)
(* . *)
(* Proof. *)
(*   revert x. rewrite TY. *)
(*   ii. clarify. des_u; ss. *)
(* Qed. *)

(* Lemma sigT_eta *)
(*       (a: { A: Type & A}) *)
(*       (b: { B: Type & B}) *)
(*       (EQTY: projT1 a = projT1 b) *)
(*       (EQVAL: projT2 a ~= projT2 b) *)
(*   : *)
(*     a = b *)
(* . *)
(* Proof. *)
(*   destruct a, b; ss. clarify. apply JMeq_eq in EQVAL. clarify. *)
(* Qed. *)

(* Class Eq {A: Type} (a0 a1: A) := { eq: a0 = a1 }. *)

(* Program Instance LeibEq_URA ra0 ra1 (EQ: Eq ra0 ra1): LeibEq (@URA.car ra0) (@URA.car ra1). *)
(* Next Obligation. inv EQ. ss. Qed. *)







Module RA.
  Class t: Type := mk {
    car:> Type;
    add: car -> car -> car;
    wf: car -> Prop;
    add_comm: forall a b, add a b = add b a;
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    wf_mon: forall a b, wf (add a b) -> wf a;

    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B => forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;
  }
  .

  Lemma extends_updatable
        `{M: t}
        a b
        (EXT: extends a b)
    :
      <<UPD: updatable b a>>
  .
  Proof.
    ii. rr in EXT. des. clarify. eapply wf_mon; et.
    rewrite <- add_assoc in H.
    rewrite <- add_assoc. rewrite (add_comm ctx). et.
  Qed.

  Lemma updatable_add
        `{M: t}
        a0 a1
        b0 b1
        (UPD0: updatable a0 a1)
        (UPD1: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. r in UPD0. r in UPD1.
    specialize (UPD0 (add b0 ctx)). exploit UPD0; et. { rewrite add_assoc. ss. } intro A.
    specialize (UPD1 (add a1 ctx)). exploit UPD1; et.
    { rewrite add_assoc. rewrite (add_comm b0). rewrite <- add_assoc. ss. }
    intro B.
    rewrite (add_comm a1). rewrite <- add_assoc. ss.
  Qed.

  Lemma extends_add
        `{M: t}
        a b delta
        (EXT: extends a b)
    :
      <<EXT: extends (add a delta) (add b delta)>>
  .
  Proof.
    rr in EXT. rr. des. exists ctx. subst. rewrite <- add_assoc. rewrite (add_comm a).
    sym. rewrite <- add_assoc. rewrite add_comm. f_equal. rewrite add_comm. ss.
  Qed.

  Section PLAYGROUND.

  Definition sub {M: t}: car -> car -> car -> Prop :=
    fun ab a b => ab = add a b
  .

  Definition refines {M: t}: car -> car -> Prop :=
    fun r_tgt r_src =>
      forall ctx, wf (add r_src ctx) -> wf (add r_tgt ctx)
  .

  Goal forall (M: t), extends <2= refines.
  Proof.
    ii. r in PR. des; clarify. rewrite add_comm in H. rewrite add_assoc in H.
    apply wf_mon in H. rewrite add_comm. ss.
  Qed.

  Goal forall (M: t), refines <2= extends.
  Proof.
    intros ? r_tgt r_src ?. r in PR; r.
    destruct (classic (exists diff, sub r_src r_tgt diff)).
    - des. r in H. subst. eauto.
    - Abort.

  Let update_horizontal
          (M: t)
          a0 a1
          b0 b1
          (UPDA: updatable a0 a1)
          (UPDB: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. rewrite <- add_assoc in H. apply UPDA in H.
    rewrite add_comm in H. rewrite <- add_assoc in H.
    apply UPDB in H. rewrite add_comm with (a:=a1). rewrite <- add_assoc.
    rewrite add_comm with (a:=a1). eauto.
  Qed.

  Let update_vertical_stupid
          (M: t)
          a0 a1 a2
          (UPDA: forall ctx, (wf (add a0 ctx) -> wf (add a1 ctx)) /\ (wf (add a1 ctx) -> wf (add a2 ctx)))
    :
      <<UPD: updatable a0 a2>>
  .
  Proof.
    ii. specialize (UPDA ctx). des. eauto.
  Qed.

  Let update_stupid
          (M: t)
          a0 a1 a2
          b0 b1
          (UPDA: forall ctx, (wf (add a0 ctx) -> wf (add a1 ctx)) /\ (wf (add a1 ctx) -> wf (add a2 ctx)))
          (UPDB: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a2 b1)>>
  .
  Proof.
    ii. rewrite <- add_assoc in H.
    specialize (UPDA (add b0 ctx)).
    apply UPDA in H. apply UPDA in H.
    rewrite add_comm in H. rewrite <- add_assoc in H.
    apply UPDB in H. rewrite add_comm with (a:=a2). rewrite <- add_assoc.
    rewrite add_comm with (a:=a2). eauto.
  Qed.

  End PLAYGROUND.

  Program Instance extends_Transitive `{M: t}: Transitive extends.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; et. rewrite add_assoc. et.
  Qed.

  Program Instance updatable_PreOrder `{M: t}: PreOrder updatable.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. r in H. r in H0. eauto. Qed.

  Program Instance prod (M0 M1: t): t := {
    car := car (t:=M0) * car (t:=M1);
    add := fun '(a0, a1) '(b0, b1) => ((add a0 b0), (add a1 b1));
    wf := fun '(a0, a1) => wf a0 /\ wf a1;
  }
  .
  Next Obligation. f_equal; rewrite add_comm; ss. Qed.
  Next Obligation. f_equal; rewrite add_assoc; ss. Qed.
  Next Obligation. split; eapply wf_mon; et. Qed.

  Theorem prod_updatable
          M0 M1
          (a0: @car M0) (a1: @car M1)
          (b0: @car M0) (b1: @car M1)
          (UPD0: updatable a0 b0)
          (UPD1: updatable a1 b1)
    :
      <<UPD: @updatable (prod M0 M1) (a0, a1) (b0, b1)>>
  .
  Proof.
    ii. ss. des_ifs. des. esplits; et.
  Qed.

  Program Instance frac (denom: positive): t := {
    car := positive;
    add := fun a b => (a + b)%positive;
    wf := fun a => (a <= denom)%positive;
  }
  .
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Theorem frac_updatable
          denom M
          a b
    :
      <<UPD: @updatable (prod (frac denom) M) (denom, a) b>>
  .
  Proof.
    ii. ss. des_ifs. des. lia.
  Qed.

  Program Instance agree (A: Type): t := {
    car := option A;
    add := fun a0 a1 => if excluded_middle_informative (a0 = a1) then a0 else None;
    wf := fun a => a <> None;
  }
  .
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.

  Theorem agree_unupdatable
          A
          a0 a1
    :
      <<UPD: @updatable (agree A) (Some a0) a1 -> a1 = Some a0>>
  .
  Proof.
    ii. ss. rr in H. specialize (H (Some a0)). ss. des_ifs. clear_tac.
    apply NNPP. ii. apply H; ss.
  Qed.

  Program Instance excl (A: Type): t := {
    car := option A;
    add := fun _ _ => None;
    wf := fun a => a <> None;
  }
  .

  Theorem excl_updatable
          A
          a0 a1
    :
      <<UPD: @updatable (excl A) (Some a0) a1>>
  .
  Proof. rr. ii. ss. Qed.

  (* Definition excl_map A B (f: A -> B) (a: option A + unit): option B + unit := *)
  (*   match a with *)
  (*   | inl oa => inl (option_map f oa) *)
  (*   | inr tt => inr tt *)
  (*   end *)
  (* . *)
  (* Instance exclC_Functor: Functor (fun A => @PCM.t (@RA.excl A)) := Build_Functor _ exclC_map. *)

  (*** exclusive <---> embracive ***)
  Program Instance embr (A: Type): t := {
    car := option A;
    add := fun _ _ => None;
    wf := fun _ => True;
  }
  .




  (* Definition boom := unit. *)
  (*** TODO: unify the style with auth_t: either use custom inductive, or just sum ***)

  (*** program instance act weirdly, so I put the definition out... ***)
  (*** TODO: fix it properly ***)
  Let sum_add {M0 M1} := (fun (a b: car (t:=M0) + car (t:=M1) + unit) =>
                            match a, b with
                            | inl (inl a0), inl (inl b0) => inl (inl (add a0 b0))
                            | inl (inr a1), inl (inr b1) => inl (inr (add a1 b1))
                            | _, _ => inr tt
                            end).
  Let sum_wf {M0 M1} := (fun (a: car (t:=M0) + car (t:=M1) + unit) =>
                           match a with
                           | inl (inl a0) => wf a0
                           | inl (inr a1) => wf a1
                           | _ => False
                           end).
  Program Instance sum (M0 M1: t): t := {
    car := car (t:=M0) + car (t:=M1) + unit (* boom *);
    add := sum_add;
    wf := sum_wf;
  }
  .
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_comm. Qed.
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_assoc. Qed.
  Next Obligation. unfold sum_wf in *. des_ifs; ss; des_ifs; eapply wf_mon; et. Qed.

  Program Instance pointwise K (M: t): t := {
    car := K -> car;
    add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    wf := fun f => forall k, wf (f k);
  }
  .
  Next Obligation. apply func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. eapply wf_mon; ss. Qed.

  Local Program Instance empty: t := {
    car := void;
    add := fun a _ => a;
    wf := bot1;
  }
  .
  Next Obligation. ss. Qed.

End RA.







Local Obligation Tactic := i; unseal "ra"; ss; des_ifs_safe.

(*** PCM == Unital RA ***)
(*** When URA, not RA? (1) Auth algebra (2) global RA construction ***)
Module URA.
  Class t: Type := mk {
    car:> Type;
    unit: car;
    _add: car -> car -> car;
    _wf: car -> Prop;
    _add_comm: forall a b, _add a b = _add b a;
    _add_assoc: forall a b c, _add a (_add b c) = _add (_add a b) c;
    add: car -> car -> car := Seal.sealing "ra" _add;
    wf: car -> Prop := Seal.sealing "ra" _wf;
    unit_id: forall a, add a unit = a;
    wf_unit: wf unit;
    wf_mon: forall a b, wf (add a b) -> wf a;

    (* extends := fun a b => exists ctx, add a ctx = b; *)
    (* updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx); *)
    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B => forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;
  }
  .

  Lemma add_comm `{M: t}: forall a b, add a b = add b a. Proof. i. unfold add. unseal "ra". rewrite _add_comm; ss. Qed.
  Lemma add_assoc `{M: t}: forall a b c, add a (add b c) = add (add a b) c. Proof. i. unfold add. unseal "ra". rewrite _add_assoc; ss. Qed.

  Lemma extends_updatable
        `{M: t}
        a b
        (EXT: extends a b)
    :
      <<UPD: updatable b a>>
  .
  Proof.
    ii. rr in EXT. des. clarify. eapply wf_mon; et.
    rewrite <- add_assoc in H.
    rewrite <- add_assoc. rewrite (add_comm ctx). et.
  Qed.

  Lemma unit_idl `{M: t}: forall a, add unit a = a. i. rewrite add_comm. rewrite unit_id; ss. Qed.

  (*** TODO: remove redundancy with "updatable_horizontal" above ***)
  Lemma updatable_add
        `{M: t}
        a0 a1
        b0 b1
        (UPD0: updatable a0 a1)
        (UPD1: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. r in UPD0. r in UPD1.
    specialize (UPD0 (add b0 ctx)). exploit UPD0; et. { rewrite add_assoc. ss. } intro A.
    specialize (UPD1 (add a1 ctx)). exploit UPD1; et.
    { rewrite add_assoc. rewrite (add_comm b0). rewrite <- add_assoc. ss. }
    intro B.
    rewrite (add_comm a1). rewrite <- add_assoc. ss.
  Qed.

  Lemma updatable_unit
        `{M: t}
        a
    :
      <<UPD: updatable a unit>>
  .
  Proof.
    ii. rewrite unit_idl. rewrite add_comm in H. eapply wf_mon; et.
  Qed.

  Lemma extends_add
        `{M: t}
        a b delta
        (EXT: extends a b)
    :
      <<EXT: extends (add a delta) (add b delta)>>
  .
  Proof.
    rr in EXT. rr. des. exists ctx. subst. rewrite <- add_assoc. rewrite (add_comm a).
    sym. rewrite <- add_assoc. rewrite add_comm. f_equal. rewrite add_comm. ss.
  Qed.

  Program Instance prod (M0 M1: t): t := {
    car := car (t:=M0) * car (t:=M1);
    unit := (unit, unit);
    _add := fun '(a0, a1) '(b0, b1) => ((add a0 b0), (add a1 b1));
    _wf := fun '(a0, a1) => wf a0 /\ wf a1;
  }
  .
  Next Obligation. f_equal; rewrite add_comm; ss. Qed.
  Next Obligation. f_equal; rewrite add_assoc; ss. Qed.
  Next Obligation. f_equal; rewrite unit_id; ss. Qed.
  Next Obligation. split; eapply wf_unit. Qed.
  Next Obligation. des. split; eapply wf_mon; et. Qed.

  Program Definition to_RA (M: t): RA.t := {|
    RA.car := car;
    RA.add := add;
    RA.wf := wf;
  |}
  .
  Next Obligation. apply add_comm. Qed.
  Next Obligation. apply add_assoc. Qed.
  Next Obligation. eapply wf_mon; et. Qed.

  Global Program Instance extends_PreOrder `{M: t}: PreOrder extends.
  Next Obligation. rr. eexists unit. ss. rewrite unit_id. ss. Qed.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; et. rewrite add_assoc. et.
  Qed.

  Program Instance updatable_PreOrder `{M: t}: PreOrder updatable.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. r in H. r in H0. eauto. Qed.






  Module of_RA.
  Section of_RA.

  Inductive car {X: Type}: Type :=
  | just (x: X): car
  | unit: car
  .

  Let wf `{M: RA.t}: car -> Prop := fun a => match a with
                                             | just a => RA.wf a
                                             | _ => True
                                             end.
  Let add `{M: RA.t}: car -> car -> car :=
    fun a b =>
      match a, b with
      | just a, just b => just (RA.add a b)
      | unit, _ => b
      | _, unit => a
      end.

  Program Instance t (RA: RA.t): URA.t := {
    car := car;
    unit := of_RA.unit;
    _wf := wf;
    _add := add;
  }.
  Next Obligation. unfold add. des_ifs. { rewrite RA.add_comm; ss. } Qed.
  Next Obligation. unfold add. des_ifs. { rewrite RA.add_assoc; ss. } Qed.
  Next Obligation. unfold add. des_ifs. Qed.
  Next Obligation. unfold add in *. des_ifs. eapply RA.wf_mon; eauto. Qed.

  End of_RA.
  End of_RA.

  (* Coercion to_RA: t >-> RA.t. *)
  Coercion of_RA.t: RA.t >-> t.

  (* Lemma eta *)
  (*       RA0 RA1 *)
  (*       (CAR: car (t:=RA0) = car (t:=RA1)) *)
  (*       (UNIT: unit (t:=RA0) ~= unit (t:=RA1)) *)
  (*       (ADD: add (t:=RA0) ~= add (t:=RA1)) *)
  (*       (WF: wf (t:=RA0) ~= wf (t:=RA1)) *)
  (*   : *)
  (*     <<EQ: RA0 = RA1>> *)
  (* . *)
  (* Proof. *)
  (*   destruct RA0, RA1; ss. subst. clarify. *)
  (*   assert(add_comm0 = add_comm1) by apply proof_irr. *)
  (*   assert(add_assoc0 = add_assoc1) by apply proof_irr. *)
  (*   assert(unit_id0 = unit_id1) by apply proof_irr. *)
  (*   assert(wf_unit0 = wf_unit1) by apply proof_irr. *)
  (*   assert(wf_mon0 = wf_mon1) by apply proof_irr. *)
  (*   subst. reflexivity. *)
  (* Qed. *)

  (* Inductive iso (RA0 RA1: t): Prop := *)
  (* | iso_intro *)
      
  (* . *)

  (* Lemma isomorphic *)
  (*       URA *)
  (*   : *)
  (*     <<EQ: of_RA (to_RA URA) = URA>> *)
  (* . *)
  (* Proof. *)
  (*   r. eapply eta; ss. *)
  (* Qed. *)









  Section AUTH.

  Inductive auth_t `{M: t}: Type :=
  | frag (f: car)
  | excl (e: car) (f: car)
  | boom
  .

  Let auth_add `{M: t} := fun a0 a1 => match a0, a1 with
                                       | frag f0, frag f1 => frag (add f0 f1)
                                       | frag f0, excl e1 f1 => excl e1 (add f0 f1)
                                       | excl e0 f0, frag f1 => excl e0 (add f0 f1)
                                       | _, _ => boom
                                       end.
  Let auth_wf `{M: t} := fun a =>
                           match a with
                           | frag f => wf f
                           | excl e f => extends f e /\ wf e
                           | boom => False
                           end.

  Program Instance auth (M: t): t := {
    car := auth_t;
    unit := frag unit;
    _add := auth_add;
    _wf := auth_wf;
  }
  .
  Next Obligation. subst auth_add auth_wf. ss. des_ifs; f_equal; eauto using add_comm. Qed.
  Next Obligation. subst auth_add auth_wf. ss. des_ifs; f_equal; eauto using add_assoc. Qed.
  Next Obligation. subst auth_add auth_wf. ss. ii; des_ifs; ss; rewrite unit_id; ss. Qed.
  Next Obligation. subst auth_add auth_wf. eauto using wf_unit. Qed.
  Next Obligation.
    subst auth_add auth_wf. ss.
    des_ifs; des; eauto using wf_mon.
    - rr in H. des. subst. eapply wf_mon. rewrite add_assoc. eauto.
    - esplits; eauto. etrans; et. rr. ss. esplits; et.
  Qed.

  End AUTH.

  Definition black `{M: t} (a: car): car (t:=auth M) := excl a unit.
  Definition white `{M: t} (a: car): car (t:=auth M) := frag a.

  Definition local_update `{M: t} a0 b0 a1 b1: Prop :=
    forall ctx, (<<WF: wf a0>> /\ <<FRAME: a0 = add b0 ctx>>) ->
                (<<WF: wf a1>> /\ <<FRAME: a1 = add b1 ctx>>)
  .

  Lemma unfold_add `{M: t}: add = _add. Proof. unfold add. unseal "ra". refl. Qed.
  (* Hint Resolve unfold_add. *)
  Lemma unfold_wf `{M: t}: wf = _wf. Proof. unfold wf. unseal "ra". refl. Qed.
  (* Hint Resolve unfold_wf. *)
  Lemma unfold_wf2 `{M: t}: forall x, wf x <-> _wf x. Proof. unfold wf. unseal "ra". refl. Qed.
  (* Hint Resolve unfold_wf2. *)
  Opaque add wf.

  Theorem auth_update
          `{M: t}
          a b a' b'
          (UPD: local_update a b a' b')
    :
      <<UPD: updatable (add (black a) (white b)) (add (black a') (white b'))>>
  .
  Proof.
    rr. rewrite unfold_add, unfold_wf in *. ii. ss. des_ifs. des.
    r in UPD. r in H. des; clarify.
    rewrite unit_idl in *. ss.
    exploit (UPD (add f0 ctx)); et.
    { esplits; et. rewrite add_assoc. ss. }
    i; des. clarify. esplits; et. rr. exists ctx. rewrite add_assoc. ss.
  Qed.

  Theorem auth_dup_black
          `{M: t}
          a ca
          (CORE: a = add a ca)
    :
      <<DUP: updatable (t:=auth M) (black a) (add (black a) (white ca))>>
  .
  Proof.
    (* r. rewrite <- unit_id at 1. *)
    (* eapply auth_update. rr. ii. des. rewrite unit_idl in FRAME. subst. *)
    (* esplits; et. rewrite add_comm; ss. *)
    rr. rewrite unfold_add, unfold_wf in *. ii. ss. des_ifs. des.
    rr in H. des. rewrite unit_idl in *. esplits; et.
    - rr. rr in H. des. esplits; et. ss. rewrite <- add_assoc. rewrite H. rewrite add_comm. eauto.
  Qed.

  Theorem auth_dup_white
          `{M: t}
          a ca
          (CORE: a = add a ca)
    :
      <<DUP: updatable (t:=auth M) (white a) (add (white a) (white ca))>>
  .
  Proof.
    rr. rewrite unfold_add, unfold_wf in *. ii. ss. des_ifs.
    - ss. rewrite <- CORE. ss.
    - ss. des. esplits; et. rewrite <- CORE. ss.
  Qed.

  Theorem auth_alloc
          `{M: t}
          a0 a1 b1
          (UPD: local_update a0 unit a1 b1)
    :
      <<UPD: updatable (t:=auth M) (black a0) (add (black a1) (white b1))>>
  .
  Proof.
    r. rewrite <- unit_id at 1. ss. eapply auth_update. ss.
  Qed.

  Theorem auth_alloc2
          `{M: t}
          a0 delta
          (WF: wf (add a0 delta))
    :
      <<UPD: updatable (t:=auth M) (black a0) (add (black (add a0 delta)) (white delta))>>
  .
  Proof.
    rr. rewrite unfold_add, unfold_wf in *.
    ii. ss. des_ifs. des.
    esplits; et.
    rewrite unit_idl in *.
    rr in H. des. rr. exists ctx; et. ss. clarify.
    rewrite add_comm. rewrite (add_comm f0). rewrite <- add_assoc. f_equal.
    rewrite add_comm. ss.
  Qed.

  Theorem auth_dealloc
          `{M: t}
          a0 a1 b0
          (UPD: local_update a0 b0 a1 unit)
    :
      <<UPD: updatable (t:=auth M) (add (black a0) (white b0)) (black a1)>>
  .
  Proof.
    r. rewrite <- unit_id. ss. eapply auth_update. ss.
  Qed.

  Theorem auth_included
          `{M: t}
          a b
          (WF: wf (add (black a) (white b)))
    :
      <<EXT: extends b a>>
  .
  Proof.
    rewrite unfold_add in WF; rewrite unfold_wf in WF.
    rr in WF. des. rr in WF. rr. des. rewrite unit_idl in WF. subst. esplits; et.
  Qed.

  Theorem auth_exclusive
          `{M: t}
          a b
          (WF: wf (add (black a) (black b)))
    :
      False
  .
  Proof. rewrite unfold_add in WF; rewrite unfold_wf in WF. ss. Qed.

  Program Instance pointwise K (M: t): t := {
    car := K -> car;
    unit := fun _ => unit;
    _add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    _wf := fun f => forall k, wf (f k);
  }
  .
  Next Obligation. apply func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite unit_id. ss. Qed.
  Next Obligation. i. eapply wf_unit; ss. Qed.
  Next Obligation. i. eapply wf_mon; ss. Qed.

  Program Instance pointwise_dep K (M: K -> t): t := {
    car := forall (k: K), car (t:=M k);
    unit := fun _ => unit;
    _add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    _wf := fun f => forall k, wf (f k);
  }
  .
  Next Obligation. apply func_ext_dep. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite unit_id. ss. Qed.
  Next Obligation. i. eapply wf_unit; ss. Qed.
  Next Obligation. i. eapply wf_mon; ss. Qed.

End URA.

(* Coercion URA.to_RA: URA.t >-> RA.t. *)
Coercion URA.of_RA.t: RA.t >-> URA.t.
Coercion RA.car: RA.t >-> Sortclass.
Coercion URA.car: URA.t >-> Sortclass.





Lemma nth_error_nth
      A (l: list A) n a d
      (NTH: nth_error l n = Some a)
  :
    <<NTH: nth n l d = a>>
.
Proof.
  ginduction n; ii; ss; des_ifs. ss. eapply IHn; et.
Qed.





Module GRA.
  Class t: Type := __GRA__INTERNAL__: (nat -> URA.t).
  Class inG (RA: URA.t) (Σ: t) := InG {
    inG_id: nat;
    (* inG_prf: Eq (GRA inG_id) RA; *)
    inG_prf: RA = Σ inG_id;
  }
  .
  Class subG (Σ0 Σ1: t) := SubG i : { j | Σ0 i = Σ1 j }.
  (* Class subG (GRA0 GRA1: t) := SubG { subG_prf: forall i, { j | GRA0 i = GRA1 j } }. *)

  Definition of_list (RAs: list URA.t): t := fun n => List.nth n RAs (URA.of_RA.t RA.empty).

  Definition to_URA (Σ: t): URA.t := URA.pointwise_dep Σ.

  Coercion to_URA: t >-> URA.t.

  Let cast_ra {A B: URA.t} (LeibEq: A = B) (a: URA.car (t:=A)): URA.car (t:=B) :=
    eq_rect A (@URA.car) a _ LeibEq.

  (* a: URA.car =ty= RAs inG_id =ty= RAs n *)
  Definition embed {A Σ} `{@GRA.inG A Σ} (a: URA.car (t:=A)): URA.car (t:=Σ) :=
    fun n => match Nat.eq_dec inG_id n with
             | left H => ((@eq_rect nat inG_id Σ ((cast_ra inG_prf a): Σ inG_id) n H): Σ n)
             | right _ => URA.unit
             end
  .

  Lemma embed_wf
        A Σ
        `{@GRA.inG A Σ}
        (a: A)
        (WF: URA.wf (embed a))
    :
      <<WF: URA.wf a>>
  .
  Proof.
    rewrite URA.unfold_wf in WF.
    r. specialize (WF inG_id). ss. unfold embed in *. des_ifs.
    unfold cast_ra in *. unfold eq_rect, eq_sym in *. dependent destruction e. destruct inG_prf. ss.
  Qed.

  Lemma embed_add
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
    :
      <<EQ: URA.add (embed a0) (embed a1) = embed (URA.add a0 a1)>>
  .
  Proof.
    rewrite URA.unfold_add in *.
    r. ss. unfold embed. apply func_ext_dep. i. des_ifs.
    - ss. unfold cast_ra. unfold eq_rect, eq_sym. destruct inG_prf. reflexivity.
    - rewrite URA.unit_id. ss.
  Qed.

  Lemma embed_updatable
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
        (UPD: URA.updatable a0 a1)
    :
      <<UPD: URA.updatable (GRA.embed a0) (GRA.embed a1)>>
  .
  Proof.
    r in UPD. ii. ss.
    rewrite URA.unfold_add in *. rewrite URA.unfold_wf in *. ss. ii.
    rename H0 into WF.
    specialize (WF k).
    unfold embed in *. des_ifs. ss.
    unfold cast_ra in *. unfold eq_rect, eq_sym in *.
    destruct H. ss.
    dependent destruction inG_prf0.
    eapply UPD. ss.
  Qed.

  Section GETSET.
    Variable ra: URA.t.
    Variable gra: t.
    Context `{@inG ra gra}.

    Section GETSET.
    Variable get: URA.car (t:=ra).
    Variable set: URA.car (t:=ra) -> unit.

    (* own & update can be lifted *)
    (* can we write spec in terms of own & update, not get & set? *)
    (* how about add / sub? *)
    Program Definition get_lifted: URA.car (t:=gra) :=
      fun n => if Nat.eq_dec n inG_id then _ else URA.unit.
    Next Obligation.
      apply (cast_ra inG_prf get).
    Defined.

    (* Program Definition set_lifted: URA.car (t:=construction gra) -> unit := *)
    (*   fun n => if Nat.eq_dec n inG_id then _ else URA.unit. *)
    (* Next Obligation. *)
    (*   apply (ra_transport inG_prf get). *)
    (* Defined. *)
    End GETSET.

    Section HANDLER.
    Variable handler: URA.car (t:=ra) -> URA.car (t:=ra).
    Local Obligation Tactic := idtac.
    Program Definition handler_lifted: URA.car (t:=gra) -> URA.car (t:=gra) :=
      fun st0 => fun n => if Nat.eq_dec n inG_id then _ else st0 n
    .
    Next Obligation.
      i. subst. simpl in st0. specialize (st0 inG_id).
      rewrite <- inG_prf in st0. specialize (handler st0). rewrite <- inG_prf. apply handler.
    Defined.

    End HANDLER.

  End GETSET.

  Section CONSTRUCTION.
    Variable RAs: list URA.t.
    Let GRA: t := (fun n => List.nth n RAs RA.empty).
    Theorem construction_adequate: forall n RA (IN: List.nth_error RAs n = Some RA),
        inG RA GRA.
    Proof.
      i. unshelve econs; eauto. unfold GRA. sym. eapply nth_error_nth; et.
    Qed.

    (* Let GRA2: RA.t := URA.pointwise_dep GRA. *)
    (* Goal @RA.car GRA2 = forall k, (@RA.car (GRA k)). ss. Qed. *)
  End CONSTRUCTION.

  (* Definition extends (RA0 RA1: URA.t): Prop := *)
  (*   exists c, URA.prod RA0 c = RA1 *)
  (* . *)

  Class inG2 (RA GRA: URA.t): Prop := {
    GRA_data: t;
    (* GRA_prf:  *)
    inG2_id: nat;
    inG2_prf: GRA_data inG2_id = RA;
  }
  .

End GRA.
Coercion GRA.to_URA: GRA.t >-> URA.t.

Notation "'ε'" := URA.unit.
Global Opaque GRA.to_URA.
Infix "⋅" := URA.add (at level 50, left associativity).
Notation "(⋅)" := URA.add (only parsing).
(* Definition ε `{Σ: GRA.t}: Σ := URA.unit. *)

(***
Choose: non-det
Take: angelic non-det
(*** empty choose : NB ***)
(*** empty take : UB ***)
x <- Choose X ;; guarantee (P x) ;; k x   (~=) x <- Choose { X | P x } ;; k x
x <- Take X   ;; assume (P x)    ;; k x   (~=) x <- Take { X | P x }   ;; k x
guarantee P ;; assume P ;; k              (~=) guarantee P ;; k
x <- Take X ;; pure ;; k x                (>=) pure ;; x <- Take X ;; k x
pure ;; x <- Choose X ;; k x              (>=) x <- Choose X ;; pure ;; k x
______________caller______________    _________________callee_________________   _caller_
x0 <- Choose X ;; guarantee (P x0) ;; (x1 <- Take X ;; assume (P x1) ;; k1 x1) ;; k0 x0
(<=)
x0 <- Choose X ;; x1 <- Take X ;; guarantee (P x0) ;; assume (P x1) ;; k1 x1 ;; k0 x0
(<=)
x <- Choose X ;; guarantee (P x) ;; assume (P x) ;; k1 x ;; k0 x
(<=)
x <- Choose X ;; guarantee (P x) ;; k1 x ;; k0 x
Goal forall X Y (k: X -> Y),
    x <- trigger (EChoose X) ;; Ret (k x) =
    y <- trigger (EChoose {y | exists x, y = k x}) ;; Ret (proj1_sig y)
.
Abort.
***)



Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.

Section TEST.
  Variable A B C: Type.
  Let _myRA: URA.t := (A ==> B ==> (RA.excl C))%ra.
  Let myRA: URA.t := URA.auth _myRA.
  Goal forall (x: URA.car (t:=_myRA)), URA.wf (URA.black x) -> URA.wf x.
  Proof. cbn. rewrite ! URA.unfold_wf. ii; ss. des. Abort.
End TEST.
