Require Import Coqlib Any.
Require Import Skeleton.
Require Import ModSem Behavior SimModSem.
Require Import PCM.
Require Import HoareDef STB.
Require Import ClightlightMem0 ClightlightMem1.
Require Import HTactics ProofMode.
From compcert Require Import Ctypes Floats Integers Values Memory AST Clight Clightdefs.


Set Implicit Arguments.

(* 
(*** black + delta --> new_black ***)
Definition add_delta_to_black `{M: URA.t} (b: Auth.t M) (w: Auth.t _): Auth.t _ :=
  match b, w with
  | Auth.excl e _, Auth.frag f1 => Auth.excl (e ⋅ f1) URA.unit
  | _, _ => Auth.boom
  end
.


(*** TODO: move to Coqlib ***)
Lemma repeat_nth_some
      X (x: X) sz ofs
      (IN: ofs < sz)
  :
    nth_error (repeat x sz) ofs = Some x
.
Proof.
  ginduction sz; ii; ss.
  - lia.
  - destruct ofs; ss. exploit IHsz; et. lia.
Qed.

Lemma repeat_nth_none
      X (x: X) sz ofs
      (IN: ~(ofs < sz))
  :
    nth_error (repeat x sz) ofs = None
.
Proof.
  generalize dependent ofs. induction sz; ii; ss.
  - destruct ofs; ss.
  - destruct ofs; ss. { lia. } hexploit (IHsz ofs); et. lia.
Qed.

Lemma repeat_nth
      X (x: X) sz ofs
  :
    nth_error (repeat x sz) ofs = if (ofs <? sz) then Some x else None
.
Proof.
  des_ifs.
  - eapply repeat_nth_some; et. apply_all_once Nat.ltb_lt. ss.
  - eapply repeat_nth_none; et. apply_all_once Nat.ltb_ge. lia.
Qed.



Ltac Ztac := all_once_fast ltac:(fun H => first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]).

Lemma _points_to_hit: forall b ofs v, (_points_to (b, ofs) [v] b ofs) = (Some v).
Proof. i. rewrite unfold_points_to. ss. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia. rewrite Z.sub_diag. ss. Qed.

Lemma _points_to_miss: forall b ofs b' ofs' (MISS: b <> b' \/ ofs <> ofs') v, (_points_to (b, ofs) [v] b' ofs') = ε.
Proof. i. rewrite unfold_points_to. ss. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia. Qed.

Lemma _points_to_disj: forall b0 ofs0 v0 b1 ofs1 v1,
    URA.wf (_points_to (b0, ofs0) [v0] ⋅ _points_to (b1, ofs1) [v1]) -> b0 <> b1 \/ ofs0 <> ofs1.
Proof.
  ii. do 2 ur in H. specialize (H b0 ofs0). rewrite _points_to_hit in H.
  rewrite unfold_points_to in H. ss. ur in H. des_ifs_safe. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia.
  assert(ofs0 = ofs1) by lia. subst. rewrite Z.sub_diag in *. ss.
Qed.

Lemma dec_true: forall X `{Dec X} (x0 x1: X), x0 = x1 -> ((dec x0 x1): bool) = true.
Proof. ii. subst. unfold dec. destruct H; ss. Qed.

Lemma dec_false: forall X `{Dec X} (x0 x1: X), x0 <> x1 -> ((dec x0 x1): bool) = false.
Proof. ii. subst. unfold dec. destruct H; ss. Qed.
(* Lemma local_update_same *)
(*       `{M: URA.t} *)
(*       x0 y0 x1 y1 *)
(*       (SAME: x0 ⋅ y0 = x1 ⋅ y1) *)
(*   : *)
(*     URA.local_update x0 y0 x1 y1 *)
(* . *)
(* Proof. *)
(*   r. ii. des. subst. esplits; et. *)
(*   - *)
(* Qed. *)
*)

Section SIMMODSEM.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memszRA Σ}.

  Inductive sim_cnt 
  : URA.car (t:=(Excl.t _)) -> (perm_kind -> option permission) -> memval -> Prop :=
  | sim_present (res : Excl.t _) perm mv p_cur p_max
      (RES: res = Some (p_cur, p_max, mv))
      (CUR: perm Cur = Some p_cur) 
      (MAX: perm Max = Some p_max) 
    : sim_cnt res perm mv
  | sim_empty mv : sim_cnt ε (fun _ => None) mv
  .

  Inductive sim_header
  : URA.car (t:=(Excl.t _)) -> Maps.ZMap.t memval 
    -> (Z -> perm_kind -> option permission) -> Prop :=
  | sim_header_malloced cnt perm sz 
      (CNT: Mem.getN (size_chunk_nat Mptr) (- size_chunk Mptr) cnt 
              = inj_bytes (encode_int (size_chunk_nat Mptr) sz))
      (PERM: forall ofs, (- size_chunk Mptr <= ofs < 0)%Z -> perm ofs Cur = Some Freeable)
    : sim_header (Some sz) cnt perm
  | sim_header_not cnt perm 
      (PERM: forall ofs, (- size_chunk Mptr <= ofs < 0)%Z -> perm ofs Cur = None)
    : sim_header ε cnt perm
  .

  Lemma sim_cnt_alloc res m m' b' lo hi
    (PRE: forall b ofs, 0 ≤ ofs ->
            sim_cnt (res b ofs) (Maps.PMap.get b (m.(Mem.mem_access)) ofs)
              (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m))))
    (ORTHO: forall b ofs, (m.(Mem.nextblock) ≤ b)%positive -> res b ofs = ε)
    (ALLOC: Mem.alloc m lo hi = (m', b'))
  :
    <<PRE': forall b ofs, 0 ≤ ofs -> not (b = b' /\ lo ≤ ofs < hi) ->
                sim_cnt (res b ofs) (Maps.PMap.get b (m'.(Mem.mem_access)) ofs)
                  (Maps.ZMap.get ofs (Maps.PMap.get b (m'.(Mem.mem_contents))))>>
    /\
    <<ORTHO: forall b ofs, (m'.(Mem.nextblock) ≤ Pos.succ b)%positive -> res b ofs = ε >>.
  Proof.
    Transparent Mem.alloc.
    splits; i; unfold Mem.alloc in ALLOC; ss; clarify; ss.
    - assert (b <> Mem.nextblock m \/ (b = Mem.nextblock m /\ not (lo ≤ ofs < hi))).
        by now destruct (Pos.eq_dec b (Mem.nextblock m)); et; right; et. des.
      + rewrite Maps.PMap.gso; et; try nia. rewrite Maps.PMap.gso; et.
      + subst. rewrite Maps.PMap.gss. rewrite Maps.PMap.gss.
        destruct (Coqlib.zle lo ofs); destruct (Coqlib.zlt ofs hi);
          ss; clarify; try nia; rewrite ORTHO; try nia; econstructor 2.
    - eapply ORTHO. nia.
    Opaque Mem.alloc.
  Qed.

  Lemma sim_cnt_store_zero res m m' b' start len
    (PRE: forall b ofs, 0 ≤ ofs -> not (b = b' /\ start ≤ ofs < start + len) ->
            sim_cnt (res b ofs) (Maps.PMap.get b (m.(Mem.mem_access)) ofs)
              (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m))))
    (ORTHO: forall b ofs, (m.(Mem.nextblock) ≤ Pos.succ b)%positive -> res b ofs = ε)
    (STORE_ZEROS: Globalenvs.R_store_zeros m b' start len (Some m'))
  :
    <<PRE': forall b ofs, 0 ≤ ofs -> not (b = b' /\ start ≤ ofs < start + len) ->
                sim_cnt (res b ofs) (Maps.PMap.get b (m'.(Mem.mem_access)) ofs)
                  (Maps.ZMap.get ofs (Maps.PMap.get b (m'.(Mem.mem_contents))))>>
    /\
    <<ORTHO: forall b ofs, (m'.(Mem.nextblock) ≤ Pos.succ b)%positive -> res b ofs = ε >>.
  Proof.
    Transparent Mem.store.
    set start as start0 in *.
    set (start0 + len) as end0 in *. unfold start0 in STORE_ZEROS.
    assert (start0 ≤ start) by nia.
    assert (start + len ≤ end0) by nia.
    clearbody start0 end0.
    remember (Some m') as optm in STORE_ZEROS.
    move STORE_ZEROS at top. revert_until STORE_ZEROS.
    induction STORE_ZEROS; i; ss; clarify.
    eapply IHSTORE_ZEROS; et; try nia; i; unfold Mem.store in e0; des_ifs_safe; ss; et.
    assert (b0 <> b \/ (b0 = b /\ (not (start0 ≤ ofs) \/ not (ofs < end0))))
      by now destruct (Pos.eq_dec b0 b); et; nia. des.
    - rewrite Maps.PMap.gso; et.
    - subst. rewrite Maps.PMap.gss.
      rewrite Mem.setN_outside; try nia. et.
    - subst. rewrite Maps.PMap.gss.
      rewrite Mem.setN_outside; et;
        replace (strings.length _) with 1%nat by refl; nia.
    Opaque Mem.store.
  Qed.

  Lemma pointwise_distr (res1 res2: ClightlightMem1._memcntRA) b ofs 
      : 
        (res1 ⋅ res2) b ofs = (res1 b ofs) ⋅ (res2 b ofs).
  Proof. unfold "⋅" at 1. unseal "ra". ss. unfold "⋅" at 1. unseal "ra". ss. Qed.

  Lemma setN_inside x l i c entry
      (IN_RANGE: (i <= x)%Z /\ (x < i + Z.of_nat (length l))%Z)
      (ENTRY: nth_error l (Z.to_nat (x - i)%Z) = Some entry)
    :
      Maps.ZMap.get x (Mem.setN l i c) = entry.
  Proof.
    assert (Z.to_nat (x - i)%Z < length l)%nat by nia.
    apply nth_error_Some in H1. destruct (nth_error _ _) eqn: E in H1; clarify.
    clear H1. move l at top. revert_until l. induction l; i; ss; try nia.
    destruct (Nat.eq_dec (Z.to_nat (x - i)) 0).
    - rewrite e in *. ss. clarify. assert (x = i) by nia. rewrite H1 in *.
      rewrite Mem.setN_outside; try nia. apply Maps.ZMap.gss. 
    - change (a :: l) with ([a] ++ l) in E. rewrite nth_error_app2 in E; ss; try nia.
      replace (Z.to_nat (x - i) - 1)%nat with (Z.to_nat (x - (i + 1))) in E by nia.
      eapply IHl; et. nia.
  Qed.


  Local Ltac solve_len := unfold encode_int, bytes_of_int, rev_if_be, inj_bytes in *; 
                            change Archi.big_endian with false in *;
                            change Archi.ptr64 with true in *; ss.
  Local Ltac case_points_to := unfold __points_to; destruct (dec _ _); destruct (Coqlib.zle _ _); destruct (Coqlib.zlt).

  Lemma sim_cnt_store_initial_data sk res c m m' perm start l b'
    (PRE: forall b ofs, 0 ≤ ofs -> not (b = b' /\ start ≤ ofs < start + init_data_list_size l) ->
            sim_cnt (res b ofs) (Maps.PMap.get b (m.(Mem.mem_access)) ofs)
              (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m))))
    (ORTHO: forall b ofs, (b' ≤ b)%positive -> res b ofs = ε)
    (FILLED_ZERO: forall ofs, start ≤ ofs < start + init_data_list_size l ->
                    Maps.ZMap.get ofs (Maps.PMap.get b' m.(Mem.mem_contents)) = Byte Byte.zero)
    (STORE_RSC: store_init_data_list sk res b' start perm l = Some c)
    (STORE_MEM: ClightlightMem0.store_init_data_list sk m b' start l = Some m')
  :
    <<PRE': forall b ofs, 0 ≤ ofs -> not (b = b' /\ start ≤ ofs < start + init_data_list_size l) ->
                sim_cnt (c b ofs) (Maps.PMap.get b (m'.(Mem.mem_access)) ofs)
                  (Maps.ZMap.get ofs (Maps.PMap.get b (m'.(Mem.mem_contents))))>>
    /\
    <<PRE'': forall ofs, 0 ≤ ofs -> start ≤ ofs < start + init_data_list_size l ->
                  match c b' ofs with
                  | Excl.just (_, _, mv) => mv = Maps.ZMap.get ofs (Maps.PMap.get b' (m'.(Mem.mem_contents)))
                  | _ => False
                  end >>
    /\
    <<ORTHO: forall b ofs, (b' < b)%positive -> c b ofs = ε >>.
  Proof.
    Transparent Mem.store.
    set start as start0 in *.
    set (start0 + init_data_list_size l) as end0 in *.
    unfold end0, start0 in STORE_RSC, STORE_MEM, FILLED_ZERO.
    unfold end0 at 2. unfold start0 at 2 3.
    assert (start0 ≤ start) by nia.
    assert (start + init_data_list_size l ≤ end0) by nia.
    assert (ORTHO': forall b ofs, ((b' = b /\ start ≤ ofs) \/ (b' < b)%positive) -> res b ofs = ε)
      by now i; des; apply ORTHO; nia.
    clearbody start0 end0. clear ORTHO.
    move l at top. revert_until l.
    induction l; i; ss; clarify.
    - splits; et; i; try nia.
    - des_ifs_safe.
      replace (Mem.nextblock m) with (Mem.nextblock m0) in * by now
        unfold ClightlightMem0.store_init_data, Mem.store in Heq; des_ifs.
      hexploit IHl.
      1,2,5,6: et.
      3:{ instantiate (1:= start0). pose proof (init_data_size_pos a). nia. }
      3:{ instantiate (1:= end0). nia. }
      { i. unfold store_init_data in Heq0.
        unfold ClightlightMem0.store_init_data, Mem.store in Heq.
        pose proof (init_data_list_size_pos l).
        des_ifs; ss; rewrite pointwise_distr;
          unfold __points_to; case_points_to; ss;
            try (subst; rewrite Maps.PMap.gss);
              try (rewrite Maps.PMap.gso; et); ss;
                try rewrite URA.unit_idl;
                  try (rewrite Mem.setN_outside; solve_len; try nia);
                    try eapply PRE; et.
        replace (strings.length _) with (Z.to_nat z) in *
            by now symmetry; apply repeat_length. nia. }
      { pose proof (init_data_list_size_pos l).
        i. unfold ClightlightMem0.store_init_data, Mem.store in Heq.
        des_ifs; ss; try rewrite Maps.PMap.gss; try rewrite Mem.setN_outside;
          solve_len; ss; try nia; try (eapply FILLED_ZERO; nia). }
      { pose proof (init_data_size_pos a). unfold store_init_data in Heq0.
        des_ifs; i; rewrite pointwise_distr; unfold __points_to; des; subst;
          try solve [case_points_to; ss; try nia;
                      try solve [rewrite URA.unit_idl; eapply ORTHO'; et; nia];
                        solve_len; nia].
        case_points_to; ss; try nia; try solve [rewrite URA.unit_idl; eapply ORTHO'; et; nia].
        replace (strings.length _) with (Z.to_nat z) in l1 by now symmetry; apply repeat_length. 
        nia. }
      i. des. splits; et. i. des.
      destruct (Coqlib.zlt ofs (start + init_data_size a)); [|eapply PRE''; nia].
      clear H5.
      replace (c b' ofs) with (c0 b' ofs).
      2:{ set (start + init_data_size a) as end' in *. clearbody end'. clear - STORE_RSC l0. 
        revert_until l. induction l; i; ss; clarify.
        des_ifs_safe. pose proof (init_data_size_pos a).
        eapply IHl with (ofs:=ofs) in STORE_RSC; try nia.
        rewrite <- STORE_RSC. unfold store_init_data in Heq.
        des_ifs; try rewrite pointwise_distr; ss;
          unfold __points_to; case_points_to; ss;
            try rewrite URA.unit_idl; et; nia. }
      replace (Maps.ZMap.get ofs (Maps.PMap.get b' (Mem.mem_contents m'))) 
        with (Maps.ZMap.get ofs (Maps.PMap.get b' (Mem.mem_contents m0))).
      2:{ set (start + init_data_size a) as end' in *. clearbody end'. clear - STORE_RSC STORE_MEM l0. 
        revert_until l. induction l; i; ss; clarify.
        des_ifs_safe. pose proof (init_data_size_pos a).
        eapply IHl with (ofs:=ofs) in STORE_RSC.
        2: et. 2: nia. 
        rewrite <- STORE_RSC. unfold ClightlightMem0.store_init_data in Heq.
        unfold store_init_data in Heq0.
        des_ifs; unfold __points_to in *; try rewrite pointwise_distr; ss;
          des_ifs; try rewrite URA.unit_idl; et;
            unfold Mem.store in Heq; des_ifs; ss;
              rewrite Maps.PMap.gss; rewrite Mem.setN_outside; et. }
      unfold ClightlightMem0.store_init_data in Heq.
      unfold store_init_data in Heq0.
      pose proof (init_data_list_size_pos l).
      des_ifs; try rewrite pointwise_distr in *; ss;
        unfold __points_to in *; case_points_to; ss;
          try solve [solve_len; des_ifs; try solve [eapply nth_error_None in Heq0; ss; nia];
                      rewrite ORTHO' in Heq1; try nia; rewrite URA.unit_id in Heq1; clarify].
      all: try solve [solve_len; destruct nth_error eqn:X; try solve [eapply nth_error_None in X; ss; nia];
                      rewrite ORTHO' in Heq1; try nia; rewrite URA.unit_id in Heq1; clarify;
                      unfold Mem.store in Heq; des_ifs_safe; ss;
                      rewrite Maps.PMap.gss; eapply setN_inside in X; solve_len; try nia; et].
      + solve_len. destruct nth_error eqn:X; try solve [eapply nth_error_None in X; ss; nia].
        rewrite ORTHO' in Heq1; try nia; rewrite URA.unit_id in Heq1; clarify.
        rewrite FILLED_ZERO; try nia. 
        rewrite nth_error_repeat in X; try nia; clarify.
      + rewrite repeat_length in g. nia.
    Opaque Mem.store.
  Qed.

  Lemma sim_cnt_drop_perm m m' res perm b lo hi
    (PRE: forall ofs, 0 ≤ ofs -> lo ≤ ofs < hi ->
                  match res b ofs with
                  | Excl.just (_, _, mv) => mv = Maps.ZMap.get ofs (Maps.PMap.get b (m.(Mem.mem_contents)))
                  | _ => False
                  end)
    (PERM: forall ofs, 0 ≤ ofs -> lo ≤ ofs < hi ->
              exists mv, res b ofs = Excl.just (perm, perm, mv))
    (DROP: Mem.drop_perm m b lo hi perm = Some m')
  :
    <<PRE': forall ofs, 0 ≤ ofs -> lo ≤ ofs < hi ->
                sim_cnt (res b ofs) (Maps.PMap.get b (m'.(Mem.mem_access)) ofs)
                  (Maps.ZMap.get ofs (Maps.PMap.get b (m'.(Mem.mem_contents))))>>.
  Proof.
    red. i. hexploit PRE; et. i. des. hexploit PERM; et. i. des.
    unfold Mem.drop_perm in DROP. des_ifs_safe.
    ss. rewrite Maps.PMap.gss. destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); try nia.
    ss. econs; et.
  Qed.

  Lemma store_rsc_perm sk res c b' start perm l
    (STORE_RSC: store_init_data_list sk res b' start perm l = Some c)
    (ORTHO: forall b ofs, (b' ≤ b)%positive -> res b ofs = ε)
  :
    <<PERM: forall ofs, 0 ≤ ofs -> start ≤ ofs < start + init_data_list_size l ->
              exists mv, c b' ofs = Excl.just (perm, perm, mv)>>.
  Proof.
    assert (ORTHO': forall b ofs, ((b' = b /\ start ≤ ofs) \/ (b' < b)%positive) -> res b ofs = ε)
      by now i; des; apply ORTHO; nia.
    clear ORTHO.
    move l at top. revert_until l. induction l; red; i; ss; try nia. des_ifs.
    destruct (Coqlib.zle (start + (init_data_size a)) ofs).
    - eapply IHl; et; try nia.
      i. unfold store_init_data in Heq.
      des_ifs; rewrite pointwise_distr;
        unfold __points_to; case_points_to; ss;
          try rewrite URA.unit_idl; try (eapply ORTHO'; et); try nia;
            solve_len; try nia.
      rewrite repeat_length in l2. nia. 
    - assert (c b' ofs = c0 b' ofs).
      { clear -STORE_RSC g. set (start + _) as end' in *. clearbody end'.
        move l at top. revert_until l. induction l; i; ss; clarify.
        des_ifs. pose proof (init_data_size_pos a).
        eapply IHl with (ofs:=ofs) in STORE_RSC; et; try nia.
        rewrite STORE_RSC. unfold store_init_data in Heq.
        des_ifs; rewrite pointwise_distr;
          unfold __points_to; case_points_to; ss; try nia;
            rewrite URA.unit_idl; et. }
      rewrite H3. unfold store_init_data in Heq.
        des_ifs; rewrite pointwise_distr;
          unfold __points_to; case_points_to; ss; solve_len; try nia.
      all: try destruct nth_error eqn: X;
            try solve [eapply nth_error_None in X; ss; nia];
              rewrite ORTHO'; try nia; rewrite URA.unit_id; et.
      rewrite repeat_length in g0. nia.
  Qed.

  Lemma alloc_store_zero_condition m m0 m1 start len b
    (ALLOC: Mem.alloc m start (start + len) = (m0, b))
    (STORE_ZEROS: Globalenvs.R_store_zeros m0 b start len (Some m1))
  :
    <<FILLED_ZERO: forall ofs, start ≤ ofs < start + len ->
                    Maps.ZMap.get ofs (Maps.PMap.get b m1.(Mem.mem_contents)) = Byte Byte.zero>>.
  Proof.
    Transparent Mem.alloc.
    Transparent Mem.store.
    unfold Mem.alloc in ALLOC. clarify.
    remember (Some m1) as optm in STORE_ZEROS.
    move STORE_ZEROS at top. revert_until STORE_ZEROS.
    induction STORE_ZEROS; red; i; ss; try nia.
    destruct (Coqlib.zlt ofs (p + 1)).
    - assert (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1)) =
                Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'))).
      { set (p + 1) as p' in *. set (n - 1) as n' in *.
        clear -l STORE_ZEROS Heqoptm. clearbody p' n'. move STORE_ZEROS at top.
        revert_until STORE_ZEROS.
        induction STORE_ZEROS; i; ss; clarify; try nia.
        rewrite IHSTORE_ZEROS; et; try nia. unfold Mem.store in e0.
        des_ifs. ss. rewrite Maps.PMap.gss. rewrite Mem.setN_outside; et. }
      rewrite H2. unfold Mem.store in e0. des_ifs. ss.
      rewrite Maps.PMap.gss. erewrite setN_inside; solve_len; try nia.
      replace (ofs - p) with 0 by nia. et.
    - hexploit IHSTORE_ZEROS; et. i. des. eapply H2. nia.
    Opaque Mem.alloc.
    Opaque Mem.store.
  Qed.


  Hint Constructors sim_cnt: core.
  Hint Constructors sim_header: core.

  Let world := unit.

  (* iprop -> (if rsc is wf, iprop rsc) *)
  Let wf: world -> Any.t * Any.t -> Prop :=
    mk_wf
      (fun _ _ _mem_tgt0 =>
         (∃ (mem_tgt0: Mem.mem) (memcnt_src0: URA.car (t:=ClightlightMem1._memcntRA)) 
            (memsz_src0: URA.car (t:=ClightlightMem1._memszRA)),
             ⌜(<<TGT: _mem_tgt0 = mem_tgt0↑>>) /\
              (<<SIM_CNT: forall b ofs, 0 <= ofs -> 
                          sim_cnt (memcnt_src0 b ofs) 
                            ((Maps.PMap.get b mem_tgt0.(Mem.mem_access)) ofs) 
                            (Maps.ZMap.get ofs (Maps.PMap.get b mem_tgt0.(Mem.mem_contents)))>>) /\
              (<<SIM_HD: forall b, sim_header (memsz_src0 b) (Maps.PMap.get b mem_tgt0.(Mem.mem_contents)) 
                                    (Maps.PMap.get b mem_tgt0.(Mem.mem_access))>>)⌝
             ** OwnM ((Auth.black memcnt_src0): URA.car (t:=memcntRA))
             ** OwnM ((Auth.black memsz_src0): URA.car (t:=memszRA))
         )%I)
  .

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  (* Ltac renamer :=
    let tmp := fresh "_tmp_" in

    match goal with
    | H: context[OwnM (Auth.black ?x)] |- _ =>
      rename x into tmp; let name := fresh "memk_src0" in rename tmp into name
    end;

    match goal with
    | |- gpaco8 _ _ _ _ _ _ _ _ _ _ _ ((?mp_tgt↑), _) =>

      repeat multimatch mp_tgt with
             | context[?g] =>
               match (type of g) with
               | Mem.t =>
                 rename g into tmp; let name := fresh "mem_tgt0" in rename tmp into name
               | _ => fail
               end
             end
    end
  . *)


  Theorem correct_mod: ModPair.sim ClightlightMem1.Mem ClightlightMem0.Mem.
  Proof.
    Transparent Mem.alloc.
    Transparent Mem.store.
    econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et; ss; swap 2 3.
    { eexists. econs; ss. eapply to_semantic.
      iIntros "H". iDestruct "H" as "[A B]". iSplits. 
      iSplitR "B"; [iSplitR "A"; [|iApply "A"]|iApply "B"]. 
      iPureIntro. splits; et.
      { clear - Σ H H0. unfold load_mem, ClightlightMem0.load_mem.
        set sk as sk' at 1 3 5. clearbody sk'.
        set ε as res. set Mem.empty as m.
        replace xH with (Mem.nextblock m) by ss.
        assert (PRE: forall b ofs, 0 <= ofs -> sim_cnt (res b ofs)
                      (Maps.PMap.get b (Mem.mem_access m) ofs)
                      (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)))) by ss.
        assert (ORTHO: forall b ofs, Pos.le (Mem.nextblock m) b -> res b ofs = ε) by ss.
        clearbody res m. revert_until sk. induction sk; ss.
        unfold alloc_global, ClightlightMem0.alloc_global.
        des_ifs; i.
        - des_ifs.
          + replace (Pos.succ (Mem.nextblock m)) with (Mem.nextblock m0) by now
              apply Mem.nextblock_alloc in Heq1; unfold Mem.drop_perm in Heq0; des_ifs.
            eapply IHsk; et.
            * i. rewrite pointwise_distr.
              unfold __points_to; case_points_to; ss; try rewrite URA.unit_idl;
                try solve [unfold Mem.alloc, Mem.drop_perm in *;
                            des_ifs_safe; ss; repeat (rewrite Maps.PMap.gso; et)];
                try (rewrite ORTHO; try nia); try rewrite URA.unit_id;
                try (destruct nth_error eqn: X; try solve [eapply nth_error_None in X; ss; nia]);
                unfold Mem.alloc, Mem.drop_perm in *; des_ifs_safe; ss;
                  repeat (rewrite Maps.PMap.gss; destruct (Coqlib.zle _ _);
                            destruct (Coqlib.zlt _ _); try nia; ss).
                rewrite Maps.PMap.gss.
                replace ofs0 with 0 in * by nia. ss. clarify. econs; et.
            * i. rewrite pointwise_distr. apply Mem.nextblock_alloc in Heq1. unfold Mem.drop_perm in Heq0.
              des_ifs. ss. rewrite ORTHO; try nia. rewrite URA.unit_id. unfold __points_to. des_ifs; bsimpl.
              des. destruct (@dec block positive_Dec b1 (Mem.nextblock m)) in Heq0; clarify. nia.
          + exfalso. unfold Mem.alloc in Heq1. clarify. unfold Mem.drop_perm in Heq0. des_ifs_safe.
            apply n. unfold Mem.range_perm, Mem.perm. ss. i. rewrite Maps.PMap.gss.
            replace ofs0 with 0 in * by nia. ss. econs.
        - des_ifs.
          + assert (Mem.nextblock m2 = Mem.nextblock m3).
            { clear -Heq4. set (gvar_init v) as l in Heq4. set 0 as p in Heq4. clearbody l p.
              revert m2 m3 p Heq4. induction l; i; ss; clarify. des_ifs_safe. eapply IHl in Heq4.
              unfold ClightlightMem0.store_init_data in Heq.  unfold Mem.store in Heq.
              des_ifs. }
            replace (Pos.succ (Mem.nextblock m)) with (Mem.nextblock m0).
            2:{ apply Mem.nextblock_alloc in Heq2. apply Globalenvs.Genv.store_zeros_nextblock in Heq3.
                unfold Mem.drop_perm in Heq1. des_ifs_safe. ss. rewrite <- H2. rewrite Heq3. et. }
            eapply IHsk; et; i.
            * ss. symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3.
              set (gvar_init v) as l in *. clearbody l.
              clear IHsk sk Heq s t ofs H1 b H2.
              hexploit sim_cnt_alloc; et. i. des. clear PRE ORTHO.
              hexploit sim_cnt_store_zero; et; ss. i. des. clear PRE' ORTHO0.
              hexploit alloc_store_zero_condition;[|et|];[et|]. i. des.
              replace (Mem.nextblock _) with b0 in Heq0
                by now unfold Mem.alloc in Heq2; ss; clarify; ss. 
              hexploit sim_cnt_store_initial_data; et.
              { i. eapply ORTHO.
                assert (Mem.nextblock m1 ≤ Pos.succ b)%positive.
                { clear - Heq2 H2. unfold Mem.alloc in Heq2. clarify. ss. nia. }
                clear - Heq3 H4. set (init_data_list_size _) as len in *.
                clearbody len. remember (Some m2) as optm in *.
                move Heq3 at top. revert_until Heq3.
                induction Heq3; i; ss; clarify.
                eapply IHHeq3; et. unfold Mem.store in e0. ss. des_ifs. }
              i. des. hexploit store_rsc_perm; et.
              { i. eapply ORTHO.
                assert (Mem.nextblock m1 ≤ Pos.succ b)%positive.
                { clear - Heq2 H2. unfold Mem.alloc in Heq2. clarify. ss. nia. }
                clear - Heq3 H4. set (init_data_list_size _) as len in *.
                clearbody len. remember (Some m2) as optm in *.
                move Heq3 at top. revert_until Heq3.
                induction Heq3; i; ss; clarify.
                eapply IHHeq3; et. unfold Mem.store in e0. ss. des_ifs. }
              i. des. hexploit sim_cnt_drop_perm; et. i. des.
              assert (PRE: forall b ofs, 
                        0 ≤ ofs -> not (b = b0 /\ 0 ≤ ofs < 0 + init_data_list_size l)
                        -> sim_cnt (c b ofs) (Maps.PMap.get b (Mem.mem_access m0) ofs)
                              (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m0)))).
              { unfold Mem.drop_perm in Heq1. ss. des_ifs. ss. i.
                destruct (Pos.eq_dec b b0); try solve [rewrite Maps.PMap.gso; et].
                subst. rewrite Maps.PMap.gss.
                destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); ss; try nia.
                eapply PRE'; et. }
              clear - PRE H4 H3.
              specialize (PRE b1 ofs0 H3).
              specialize (H4 ofs0 H3).
              set (fun P => P \/ not P) as lem.
              assert (lem (b1 = b0 /\ 0 ≤ ofs0 < 0 + init_data_list_size l))
                by now unfold lem; nia. unfold lem in H.
              destruct H as [[? ?]| ?]; subst; [eapply H4|eapply PRE]; et.
            * assert (Mem.nextblock m3 = Mem.nextblock m0).
              { clear -Heq1. unfold Mem.drop_perm in Heq1. des_ifs. }
              assert (Mem.nextblock m1 = Mem.nextblock m2).
              { clear -Heq3. symmetry in Heq3.
                eapply Globalenvs.R_store_zeros_correct in Heq3.
                remember (Some m2) as optm. revert m2 Heqoptm.
                induction Heq3; i; ss; clarify.
                unfold Mem.store in e0. des_ifs. ss. eapply IHHeq3; et. }
              rewrite <- H4 in H3. rewrite <- H2 in H3. rewrite <- H5 in H3.
              clear - H3 Heq2 ORTHO Heq0. set (gvar_init v) as l in *. clearbody l.
              unfold Mem.alloc in Heq2. ss. clarify. ss. set 0 as start in *.
              clearbody start. 
              assert (ORTHO': forall b ofs, ((Mem.nextblock m = b /\ start ≤ ofs) \/ (Mem.nextblock m < b)%positive) -> res b ofs = Excl.unit)
                by now i; des; apply ORTHO; nia. clear ORTHO.
              move l at top. revert_until l.
              induction l; i; ss; clarify.
              { eapply ORTHO'. nia. }
              des_ifs_safe. eapply IHl; et.
              i. unfold store_init_data in Heq.
              des_ifs; try rewrite pointwise_distr;
              unfold __points_to; case_points_to; ss; try nia;
              try rewrite URA.unit_idl; try eapply ORTHO'; try nia; cycle 8.
              { replace Archi.ptr64 with true in * by refl. nia. }
              all: solve_len; destruct nth_error eqn: X; try solve [eapply nth_error_None in X; ss; nia]; try nia.
              { rewrite repeat_length in l1. nia. }
          + exfalso. unfold Mem.drop_perm in Heq1. des_ifs. eapply n.
            assert (Mem.range_perm m0 b0 0 (init_data_list_size (gvar_init v)) Cur Freeable).
            { unfold Mem.alloc in Heq2. clarify. unfold Mem.range_perm, Mem.perm.
              ss. rewrite Maps.PMap.gss. i.
              destruct (Coqlib.zle _ _); destruct (Coqlib.zlt); ss; try nia. econs. }
            assert (Mem.range_perm m1 b0 0 (init_data_list_size (gvar_init v)) Cur Freeable).
            { clear - Heq3 H2. set (init_data_list_size _) as end' in *.
              unfold end' in Heq3. set (init_data_list_size _) as len in Heq3.
              set 0 as start in *. unfold start in Heq3. set 0 as start' in Heq3.
              assert (start ≤ start') by nia. assert (start' + len ≤ end') by nia.
              clearbody end' len start start'.
              symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3.
              remember (Some m1) as optm in Heq3.
              move Heq3 at top. revert_until Heq3. 
              induction Heq3; i; ss; clarify. eapply IHHeq3; et; try nia.
              unfold Mem.store in e0. des_ifs. }
            clear - Heq4 H3. set (gvar_init v) as l in *.
            set 0 as start in *. unfold start in Heq4. set 0 as start' in Heq4.
            set (init_data_list_size l) as end' in *.
            assert (start ≤ start') by nia.
            assert (start' + (init_data_list_size l) ≤ end') by nia.
            clearbody end' l start start'.
            move l at top. revert_until l. 
            induction l; i; ss; clarify. des_ifs_safe.
            pose proof (init_data_size_pos a).
            eapply IHl; et; try nia.
            unfold ClightlightMem0.store_init_data, Mem.store in Heq. des_ifs.
          + exfalso. 
            ss. symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3.
            set (gvar_init v) as l in *. clearbody l.
            assert (Mem.range_perm m0 b0 0 (init_data_list_size l) Cur Freeable).
            { unfold Mem.alloc in Heq2. clarify. unfold Mem.range_perm, Mem.perm.
              ss. rewrite Maps.PMap.gss. i.
              destruct (Coqlib.zle _ _); destruct (Coqlib.zlt); ss; try nia. econs. }
            assert (Mem.range_perm m1 b0 0 (init_data_list_size l) Cur Freeable).
            { clear - Heq3 H2. set (init_data_list_size _) as end' in *.
              unfold end' in Heq3. set (init_data_list_size _) as len in Heq3.
              set 0 as start in *. unfold start in Heq3. set 0 as start' in Heq3.
              assert (start ≤ start') by nia. assert (start' + len ≤ end') by nia.
              clearbody end' len start start'.
              remember (Some m1) as optm in Heq3.
              move Heq3 at top. revert_until Heq3. 
              induction Heq3; i; ss; clarify. eapply IHHeq3; et; try nia.
              unfold Mem.store in e0. des_ifs. }
            replace (Mem.nextblock _) with b0 in Heq0
              by now unfold Mem.alloc in Heq2; ss; clarify; ss. 
            clear - H3 Heq4 Heq0. 
            set 0 as start in *. set (init_data_list_size l) as end' in H3.
            set start as start' in Heq0, Heq4. assert (start ≤ start') by nia.
            assert (start' + init_data_list_size l ≤ end') by nia.
            clearbody start' start end'. move l at top. revert_until l.
            induction l; i; ss; clarify. des_ifs.
            * pose proof (init_data_size_pos a).
              eapply IHl. 1,2: et.
              2:{ instantiate (1:=start). nia. }
              2:{ instantiate (1:=end'). nia. }
              clear - Heq H3. unfold ClightlightMem0.store_init_data, Mem.store in Heq.
              unfold Mem.range_perm, Mem.perm in *. i.
              des_ifs; ss; eapply H3; try nia.
            * clear - Heq1 Heq H3 H H0. pose proof (init_data_list_size_pos l).
              unfold ClightlightMem0.store_init_data, Mem.store in Heq.
              unfold store_init_data in Heq1. des_ifs; try eapply n; try eapply n0.
              all: unfold Mem.valid_access; ss; split; et.
              all: unfold Mem.range_perm, Mem.perm, Mem.perm_order' in *; i;
                    hexploit (H3 ofs); try nia.
              7:{ unfold Mptr in *. replace Archi.ptr64 with true in * by refl. ss. nia. }
              all: intro X; des_ifs; inv X; econs.
          + exfalso.
            assert (Mem.range_perm m0 b0 0 (init_data_list_size (gvar_init v)) Cur Freeable).
            { unfold Mem.alloc in Heq2. clarify. unfold Mem.range_perm, Mem.perm.
              ss. rewrite Maps.PMap.gss. i.
              destruct (Coqlib.zle _ _); destruct (Coqlib.zlt); ss; try nia. econs. }
            clear - Heq3 H2. set (init_data_list_size _) as end' in *.
            unfold end' in Heq3. set (init_data_list_size _) as len in Heq3.
            set 0 as start in *. unfold start in Heq3. set 0 as start' in Heq3.
            assert (start ≤ start') by nia. assert (start' + len ≤ end') by nia.
            clearbody end' len start start'.
            symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3.
            remember None as optm in Heq3.
            move Heq3 at top. revert_until Heq3. 
            induction Heq3; i; ss; clarify.
            * eapply IHHeq3 with (start:=start) (end':=end'); et; try nia.
              unfold Mem.store in e0. des_ifs.
            * unfold Mem.store in e0. des_ifs. apply n0.
              econs; ss; try solve [unfold Z.divide; exists p; nia].
              unfold Mem.range_perm, Mem.perm, Mem.perm_order' in *. i.
              hexploit H2. { instantiate (1:=ofs). nia. } i. des_ifs.
              inv H3; econs.
          + exfalso.
            replace (Mem.nextblock m) with b0 in *
              by now unfold Mem.alloc in Heq2; ss; clarify; ss.
            clear - ORTHO Heq0 Heq4. set 0 as start in *. clearbody start.
            assert (ORTHO': forall b ofs, ((b0 = b /\ start ≤ ofs) \/ (b0 < b)%positive) -> res b ofs = Excl.unit)
              by now i; des; apply ORTHO; nia. clear ORTHO.
            set (gvar_init v) as l in *. clearbody l. move l at top. revert_until l.
            induction l; i; ss; clarify. des_ifs.
            { eapply IHl; et. i. unfold store_init_data in Heq1.
              des_ifs; try rewrite pointwise_distr;
              unfold __points_to; case_points_to; ss; try nia;
              try rewrite URA.unit_idl; try eapply ORTHO'; try nia; cycle 8.
              { replace Archi.ptr64 with true in * by refl. nia. }
              all: solve_len; destruct nth_error eqn: X; try solve [eapply nth_error_None in X; ss; nia]; try nia.
              { rewrite repeat_length in l1. nia. } }
            unfold store_init_data, ClightlightMem0.store_init_data in *.
            des_ifs; try solve [unfold Mem.store in Heq; des_ifs_safe;
                                unfold Mem.valid_access in v0; des; ss]. }
      i. set ε as r. assert (r b = ε) by ss. rewrite H1. clear H1 r. econs. i. clear -H1.
      unfold ClightlightMem0.load_mem. set sk as sk' at 1. clearbody sk'.
      set Mem.empty as m. assert (Maps.PMap.get b (Mem.mem_access m) ofs Cur = None) by ss.
      clearbody m. revert_until sk. induction sk; i; ss.
      des_ifs. eapply IHsk; et. unfold ClightlightMem0.alloc_global in Heq. des_ifs.
      - unfold Mem.alloc in Heq1. unfold Mem.drop_perm in Heq. clarify. des_ifs_safe. ss.
        destruct (dec b (Mem.nextblock m)).
        + subst. rewrite Maps.PMap.gss.
          destruct (Coqlib.zle _ _); try nia.
          destruct (Coqlib.zlt _ _); try nia. ss. rewrite Maps.PMap.gss.
          destruct (Coqlib.zle _ _); try nia.
          destruct (Coqlib.zlt _ _); try nia. ss.
        + rewrite Maps.PMap.gso; et. rewrite Maps.PMap.gso; et.
      - assert (Maps.PMap.get b (Mem.mem_access m1) ofs Cur = None).
        { unfold Mem.alloc in Heq1. clarify. ss.
          destruct (Pos.eq_dec b (Mem.nextblock m));
            [subst; rewrite Maps.PMap.gss|rewrite Maps.PMap.gso; et].
          destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); ss; try nia. }
        assert (Maps.PMap.get b (Mem.mem_access m2) ofs Cur = None).
        { clear - H0 H1 Heq2. set 0 as start in Heq2.
          assert (0 ≤ start) by nia. set (init_data_list_size _) as len in Heq2.
          clearbody start len. symmetry in Heq2. remember (Some m2) as optm in Heq2.
          apply Globalenvs.R_store_zeros_correct in Heq2.
          move Heq2 at top. revert_until Heq2.
          induction Heq2; i; ss; clarify.
          eapply IHHeq2; et; try nia. unfold Mem.store in e0. des_ifs. }
        assert (Maps.PMap.get b (Mem.mem_access m3) ofs Cur = None).
        { clear - H2 H1 Heq3. set 0 as start in Heq3.
          assert (0 ≤ start) by nia. set (gvar_init v) as l in Heq3.
          clearbody start l. move l at top. revert_until l.
          induction l; i; ss; clarify. des_ifs_safe.
          pose proof (init_data_size_pos a).
          eapply IHl; et; try nia. unfold ClightlightMem0.store_init_data, Mem.store in Heq.
          des_ifs. }
        clear - H3 H1 Heq. unfold Mem.drop_perm in Heq. des_ifs_safe. ss.
        destruct (Pos.eq_dec b b0);
          [subst; rewrite Maps.PMap.gss|rewrite Maps.PMap.gso; et].
        destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); ss; try nia. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    econs; ss.
    { admit. }
    Unshelve. exact tt.
  Admitted.

  (* Theorem correct_modsem: forall sk, ModSemPair.sim (SModSem.to_tgt (to_stb [])
                                           (Mem1.SMemSem (negb ∘ csl) sk)) (Mem0.MemSem csl sk).
  Proof.
   econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
   { ss. }
    { ss. eexists. econs; ss. eapply to_semantic.
      iIntros "H". iSplits; ss; et.
      { iPureIntro. ii. unfold Mem.load_mem, initial_mem_mr.
        cbn. uo. des_ifs; et; try (by econs; et). }
      { iPureIntro. ii. ss. uo. des_ifs.
        apply nth_error_Some. ii. clarify. }
    }





    econs; ss.
    { unfold allocF. init.
      harg. fold wf. steps. hide_k. rename x into sz.
      { mDesAll; ss. des; subst.
        des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. des_ifs; clarify.
        2:{ bsimpl; des; ss; apply sumbool_to_bool_false in Heq; try lia. }
        steps. astart 0. astop.
        renamer.
        set (blk := mem_tgt0.(Mem.nb) + x).

        mAssert _ with "INV" as "INV".
        { iApply (OwnM_Upd with "INV").
          eapply Auth.auth_alloc2.
          instantiate (1:=(_points_to (blk, 0%Z) (repeat (Vundef) sz))).
          mOwnWf "INV".
          clear - WF0 WFTGT SIM.
          ss. do 2 ur. ii. rewrite unfold_points_to. des_ifs.
          - bsimpl. des. des_sumbool. subst. hexploit (SIM blk k0); et. intro T.
            inv T; eq_closure_tac.
            + exploit WFTGT; et. i; des. lia.
            + rewrite URA.unit_idl. Ztac. rewrite repeat_length in *. rewrite Z.sub_0_r. rewrite repeat_nth_some; [|lia]. ur. ss.
          - rewrite URA.unit_id. do 2 eapply lookup_wf. eapply Auth.black_wf; et.
        }
        mUpd "INV". mDesOwn "INV". steps.

        force_l. eexists. steps. hret _; ss. iModIntro. iSplitR "A"; cycle 1.
        { iSplitL; ss. iExists _. iSplitR; ss. }
        iExists _, _. iSplitR; ss. iPureIntro. esplits; et.
        - i. destruct (mem_tgt0.(Mem.cnts) blk ofs) eqn:T.
          { exfalso. exploit WFTGT; et. i; des. lia. }
          ss. do 2 ur.
          exploit SIM; et. rewrite T. intro U. inv U. rewrite unfold_points_to. ss. rewrite repeat_length.
          destruct (dec b blk); subst; ss.
          * unfold update. des_ifs_safe. rewrite <- H1. rewrite URA.unit_idl.
            rewrite Z.sub_0_r. rewrite Z.add_0_l. des_ifs.
            { bsimpl. des. Ztac. rewrite repeat_nth_some; try lia. econs. }
          * rewrite URA.unit_id. unfold update. des_ifs.
        - clear - WFTGT. ii. ss. unfold update in *. des_ifs. exploit WFTGT; et. i; des. r. lia.
      }
    }





    econs; ss.
    { unfold freeF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst.
        des_ifs; mDesAll; ss. des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer. rename n into b. rename z into ofs.
        rename a into v. rename WF into SIMWF.
        mCombine "INV" "A". mOwnWf "INV".
        assert(HIT: memk_src0 b ofs = (Some v)).
        { clear - WF.
          dup WF. eapply Auth.auth_included in WF. des. eapply pw_extends in WF. eapply pw_extends in WF.
          spc WF. rewrite _points_to_hit in WF.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        set (memk_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs
                                         then (ε: URA.car (t:=Excl.t _)) else memk_src0 _b _ofs).
        assert(WF': URA.wf (memk_src1: URA.car (t:=Mem1._memRA))).
        { clear - WF. unfold memk_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des.
          des_ifs; et.
          - rp; [eapply URA.wf_unit|ss].
          - do 2 eapply lookup_wf; et.
        }
        hexploit (SIM b ofs); et. rewrite HIT. intro B. inv B.
        force_r.
        { unfold Mem.free in *. des_ifs. }
        rename t into mem_tgt1.

        mAssert _ with "INV" as "INV".
        { iApply (OwnM_Upd with "INV").
          Local Transparent points_to.
          eapply Auth.auth_dealloc.
          instantiate (1:=memk_src1).
          clear - WF'.

          r. i. rewrite URA.unit_idl.
          Local Opaque Mem1._memRA.
          ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify.
          esplits; et.
          Local Transparent Mem1._memRA.
          unfold memk_src1. ss.
          apply func_ext. intro _b. apply func_ext. intro _ofs.
          des_ifs.
          - bsimpl; des; des_sumbool; subst.
            subst memk_src1. do 2 ur in WF'. do 2 spc WF'. des_ifs; bsimpl; des; des_sumbool; ss.
            clear - H0.
            do 2 ur in H0.
            specialize (H0 b ofs). rewrite _points_to_hit in H0. eapply Excl.wf in H0. des; ss.
          - rewrite unfold_points_to in *. do 2 ur. do 2 ur in H0.
            bsimpl. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia; try rewrite URA.unit_idl; try refl.
        }
        mUpd "INV".
        steps. force_l. eexists. steps. hret _; ss. iModIntro. iSplitL; cycle 1.
        { iPureIntro. ss. }
        iExists _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et.
        - { i. unfold Mem.free in _UNWRAPU. des_ifs. ss.
            subst memk_src1. ss.
            destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
            - unfold update. des_ifs.
            - des_ifs.
              { Psimpl. bsimpl; des; des_sumbool; ss; clarify. }
              replace (update (Mem.cnts mem_tgt0) b (update (Mem.cnts mem_tgt0 b) ofs None) b0 ofs0) with
                  (Mem.cnts mem_tgt0 b0 ofs0); cycle 1.
              { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
              et.
          }
        - clear - _UNWRAPU WFTGT. ii. unfold Mem.free in *. des_ifs. ss.
          unfold update in *. des_ifs; eapply WFTGT; et.
      }
    }





    econs; ss.
    { unfold loadF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer. rename n into b. rename z into ofs.
        rename WF into SIMWF.
        mCombine "INV" "A". mOwnWf "INV".
        assert(T: memk_src0 b ofs = (Some v)).
        { clear - WF.
          dup WF.
          eapply Auth.auth_included in WF. des.
          eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF. des; ss.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        hexploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
        mDesOwn "INV".
        force_r; ss. clarify. steps. force_l. esplits. steps.
        hret _; ss. iModIntro. iFrame. iSplitL; et.
      }
    }





    econs; ss.
    { unfold storeF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
        rename n into b. rename z into ofs. rename v into v1.
        rename a into v0. rename WF into SIMWF.
        steps.
        mCombine "INV" "A". mOwnWf "INV".
        assert(T: memk_src0 b ofs = (Some v0)).
        { clear - WF.
          dup WF.
          eapply Auth.auth_included in WF. des.
          eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF.
          des; ss.
          eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        hexploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.store. des_ifs. steps.
        set (memk_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs then (Some v1: URA.car (t:=Excl.t _)) else memk_src0 _b _ofs).
        assert(WF': URA.wf (memk_src1: URA.car (t:=Mem1._memRA))).
        { clear - WF. unfold memk_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des.
          des_ifs; et.
          - bsimpl; des; des_sumbool; subst. ur; ss.
          - do 2 eapply lookup_wf; et.
        }
        mAssert _ with "INV" as "INV".
        { iApply (OwnM_Upd with "INV").
          eapply Auth.auth_update with (a':=memk_src1) (b':=_points_to (b, ofs) [v1]); et.
          clear - wf WF'. ii. des. subst. esplits; et.
          do 2 ur in WF'. do 2 spc WF'.
          subst memk_src1. ss. des_ifs; bsimpl; des; des_sumbool; ss.
          do 2 ur. do 2 (apply func_ext; i). des_ifs.
          - bsimpl; des; des_sumbool; subst. rewrite _points_to_hit.
            do 2 ur in WF. do 2 spc WF. rewrite _points_to_hit in WF. eapply Excl.wf in WF. rewrite WF. ur; ss.
          - bsimpl; des; des_sumbool; rewrite ! _points_to_miss; et.
        }
        mUpd "INV". mDesOwn "INV".

        mEval ltac:(fold (points_to (b,ofs) [v1])) in "A".
        force_l. eexists. steps.
        hret _; ss. iModIntro. iFrame. iSplitL; ss; et.
        iExists _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et.
        - ii. cbn. des_ifs.
          + bsimpl; des; des_sumbool; subst. do 2 spc SIM. rewrite T in *. inv SIM.
            unfold memk_src1. rewrite ! dec_true; ss. econs.
          + replace (memk_src1 b0 ofs0) with (memk_src0 b0 ofs0); et.
            unfold memk_src1. des_ifs; bsimpl; des; des_sumbool; clarify; ss.
        - ii. ss. des_ifs.
          + bsimpl; des; des_sumbool; subst. eapply WFTGT; et.
          + eapply WFTGT; et.
      }
    }





    econs; ss.
    { unfold cmpF. init.
      harg. fold wf. steps. hide_k.
      { des_ifs_safe (mDesAll; ss). des; subst. clarify.
        steps. unhide_k. steps. astart 0. astop.
        renamer.
        rename b into result. rename c into resource. rename WF into SIMWF.
        assert (VALIDPTR: forall b ofs v (WF: URA.wf ((Auth.black (memk_src0: URA.car (t:=Mem1._memRA))) ⋅ ((b, ofs) |-> [v]))),
                   Mem.valid_ptr mem_tgt0 b ofs = true).
        { clear - SIM. i. cut (memk_src0 b ofs = Some v).
          - i. unfold Mem.valid_ptr.
            specialize (SIM b ofs). rewrite H in *. inv SIM. ss.
          - clear - WF.
            dup WF.
            eapply Auth.auth_included in WF. des.
            eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF.
            des; ss.
            eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et.
        }
        steps.
        mCombine "INV" "A". mOwnWf "INV". Fail mDesOwn "INV". (*** TODO: BUG!! FIXME ***)

        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et. ss. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et. ss. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et; cycle 1.
          { rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. }
          erewrite VALIDPTR; et; cycle 1.
          { erewrite URA.add_comm with (a:=(a, a0) |-> [a1]) in WF.
            rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. }
          rewrite URA.add_comm in WF. eapply URA.wf_mon in WF. ur in WF; ss. steps.
          replace (dec a a2 && dec a0 a3 ) with false; cycle 1.
          { clear - WF.
            exploit _points_to_disj; et. intro NEQ. des; try (by rewrite dec_false; ss).
            erewrite dec_false with (x0:=a0); ss. rewrite andb_false_r; ss.
          }
          steps. force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        mDesOr "PRE".
        { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          erewrite VALIDPTR; et. ss. steps. rewrite ! dec_true; ss. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
        { mDesAll; subst. des; subst. rewrite Any.upcast_downcast in *. clarify. steps.
          force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et.
        }
      }
    }
  Unshelve.
    all: ss. all: try exact 0.
  Qed. *)

  Theorem correct: refines2 [ClightlightMem0.Mem] [ClightlightMem1.Mem].
  Proof.
    eapply adequacy_local2. eapply correct_mod.
  Qed.

End PROOF.
