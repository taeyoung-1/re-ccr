Require Import CoqlibCCR Any.
Require Import Skeleton.
Require Import ModSem Behavior SimModSem.
Require Import PCM.
Require Import HoareDef STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightDmMem0 ClightDmMem1 ClightDmMemAux.
From compcert Require Import Ctypes Floats Integers Values Memory AST Clight Clightdefs IntPtrRel.


(*  *)
(* Set Implicit Arguments. *)

(* (*  *)
(* (*** black + delta --> new_black ***) *)
(* Definition add_delta_to_black `{M: URA.t} (b: Auth.t M) (w: Auth.t _): Auth.t _ := *)
(*   match b, w with *)
(*   | Auth.excl e _, Auth.frag f1 => Auth.excl (e ⋅ f1) URA.unit *)
(*   | _, _ => Auth.boom *)
(*   end *)
(* . *)


(* (*** TODO: move to CoqlibCCR ***) *)




(* Ltac Ztac := all_once_fast ltac:(fun H => first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]). *)

(* Lemma _points_to_hit: forall b ofs v, (_points_to (b, ofs) [v] b ofs) = (Some v). *)
(* Proof. i. rewrite unfold_points_to. ss. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia. rewrite Z.sub_diag. ss. Qed. *)

(* Lemma _points_to_miss: forall b ofs b' ofs' (MISS: b <> b' \/ ofs <> ofs') v, (_points_to (b, ofs) [v] b' ofs') = ε. *)
(* Proof. i. rewrite unfold_points_to. ss. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia. Qed. *)

(* Lemma _points_to_disj: forall b0 ofs0 v0 b1 ofs1 v1, *)
(*     URA.wf (_points_to (b0, ofs0) [v0] ⋅ _points_to (b1, ofs1) [v1]) -> b0 <> b1 \/ ofs0 <> ofs1. *)
(* Proof. *)
(*   ii. do 2 ur in H. specialize (H b0 ofs0). rewrite _points_to_hit in H. *)
(*   rewrite unfold_points_to in H. ss. ur in H. des_ifs_safe. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia. *)
(*   assert(ofs0 = ofs1) by lia. subst. rewrite Z.sub_diag in *. ss. *)
(* Qed. *)

(* Lemma dec_true: forall X `{Dec X} (x0 x1: X), x0 = x1 -> ((dec x0 x1): bool) = true. *)
(* Proof. ii. subst. unfold dec. destruct H; ss. Qed. *)

(* Lemma dec_false: forall X `{Dec X} (x0 x1: X), x0 <> x1 -> ((dec x0 x1): bool) = false. *)
(* Proof. ii. subst. unfold dec. destruct H; ss. Qed. *)
(* (* Lemma local_update_same *) *)
(* (*       `{M: URA.t} *) *)
(* (*       x0 y0 x1 y1 *) *)
(* (*       (SAME: x0 ⋅ y0 = x1 ⋅ y1) *) *)
(* (*   : *) *)
(* (*     URA.local_update x0 y0 x1 y1 *) *)
(* (* . *) *)
(* (* Proof. *) *)
(* (*   r. ii. des. subst. esplits; et. *) *)
(* (*   - *) *)
(* (* Qed. *) *)
(* *) *)
(* *)
Section SIMMODSEM.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition Q1 : Qp := 1%Qp.

  (* permission sim for points to *)
  Inductive sim_cnt
  : URA.car (t:=(Consent.t _)) -> (perm_kind -> option permission) -> memval ->  Prop :=
  | sim_cnt_readable (res: Consent.t _) q mv perm p
      (RES: res = Consent.just q mv)
      (Qwf: (q ≤ Q1)%Qp)
      (PERM: perm Cur = Some p)
      (Qread: perm_order p Readable)
      (Qwrite: q = Q1 -> perm_order p Writable)
    : sim_cnt res perm mv
  (* this condition is okay to be relaxed *)
  | sim_empty mv : sim_cnt ε (fun _ => None) mv
  .

  (* permission sim for allocated with, block size *)
  Inductive sim_allocated
  : URA.car (t:=(Consent.t tag)) -> URA.car (t:=(OneShot.t Z)) -> (Z -> perm_kind -> option permission) -> Maps.ZMap.t memval -> Prop :=
  | sim_allocated_nonempty (res: Consent.t _) (sres: OneShot.t _) perm cnt q tag sz init minp
      (RES: res = Consent.just q tag)
      (SRES: sres = OneShot.white sz)
      (DYNAMIC: tag = Dynamic -> Mem.getN (size_chunk_nat Mptr) (- size_chunk Mptr) cnt = inj_bytes (encode_int (size_chunk_nat Mptr) sz) /\ init = - size_chunk Mptr)
      (COMMON: tag <> Dynamic -> init = 0)
      (Qwf: (q ≤ Q1)%Qp)
      (Qnonempty: (q < Q1)%Qp -> minp = Nonempty)
      (Qfree: q = Q1 -> minp = Freeable)
      (PERMinrange: forall ofs, init <= ofs < sz -> exists p, perm ofs Cur = Some p /\ perm_order p minp)
      (PERMoutrange: forall ofs, ~ (init <= ofs < sz) -> perm ofs Cur = None)
    : sim_allocated res sres perm cnt
  | sim_allocated_empty sres perm cnt : sim_allocated ε sres perm cnt
  .

  (* block underlying concrete address sim *)
  Inductive sim_concrete
  : URA.car (t:=(OneShot.t ptrofs)) -> option Z -> Prop :=
  | sim_captured cres base
      (RES: cres = OneShot.white base):
    sim_concrete cres (Some (Ptrofs.unsigned base))
  | sim_logical cres
      (RES: cres = OneShot.black):
    sim_concrete cres None
  .


  (* Lemma sim_cnt_alloc res m m' b' lo hi
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
    Local Transparent Mem.alloc.
    splits; i; unfold Mem.alloc in ALLOC; ss; clarify; ss.
    - assert (b <> Mem.nextblock m \/ (b = Mem.nextblock m /\ not (lo ≤ ofs < hi))).
        by now destruct (Pos.eq_dec b (Mem.nextblock m)); et; right; et. des.
      + rewrite Maps.PMap.gso; et; try nia. rewrite Maps.PMap.gso; et.
      + subst. do 2 rewrite Maps.PMap.gss.
        assert (Coqlib.proj_sumbool (Coqlib.zle lo ofs) && Coqlib.proj_sumbool (Coqlib.zlt ofs hi) = false).
        { destruct (Coqlib.zle lo ofs); destruct (Coqlib.zlt ofs hi); ss; try lia. }
        rewrite H5. rewrite ORTHO; [|lia]. econs 3.
    - eapply ORTHO. nia.
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
    Local Transparent Mem.store.
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
  Qed.



  Lemma sim_cnt_store_initial_data sk res c m m' perm start l b'
    (PRE: forall b ofs, 0 ≤ ofs -> not (b = b' /\ start ≤ ofs < start + init_data_list_size l) ->
            sim_cnt (res b ofs) (Maps.PMap.get b (m.(Mem.mem_access)) ofs)
              (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m))))
    (ORTHO: forall b ofs, (b' ≤ b)%positive -> res b ofs = ε)
    (FILLED_ZERO: forall ofs, start ≤ ofs < start + init_data_list_size l ->
                    Maps.ZMap.get ofs (Maps.PMap.get b' m.(Mem.mem_contents)) = Byte Byte.zero)
    (STORE_RSC: store_init_data_list sk res b' start perm l = Some c)
    (STORE_MEM: ClightDmMem0.store_init_data_list sk m b' start l = Some m')
  :
    <<PRE': forall b ofs, 0 ≤ ofs -> not (b = b' /\ start ≤ ofs < start + init_data_list_size l) ->
                sim_cnt (c b ofs) (Maps.PMap.get b (m'.(Mem.mem_access)) ofs)
                  (Maps.ZMap.get ofs (Maps.PMap.get b (m'.(Mem.mem_contents))))>>
    /\
    <<PRE'': forall ofs, 0 ≤ ofs -> start ≤ ofs < start + init_data_list_size l ->
                  match c b' ofs with
                  | Consent.just q mv => mv = Maps.ZMap.get ofs (Maps.PMap.get b' (m'.(Mem.mem_contents)))
                  | _ => False
                  end >>
    /\
    <<ORTHO: forall b ofs, (b' < b)%positive -> c b ofs = ε >>.
  Proof.
    Local Transparent Mem.store.
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
        unfold ClightDmMem0.store_init_data, Mem.store in Heq; des_ifs.
      hexploit IHl.
      1, 2, 3, 4, 7, 8: et.
      (* 1,2,5,6: et. *)
      3:{ instantiate (1:= start0). pose proof (init_data_size_pos a). nia. }
      3:{ instantiate (1:= end0). nia. }
      { i. unfold store_init_data in Heq0.
        unfold ClightDmMem0.store_init_data, Mem.store in Heq.
        pose proof (init_data_list_size_pos l).
        (* des_ifs; ss; do 2 ur. *)
        (*   unfold __points_to; try case_points_to; ss; *)
        (*     try (subst; rewrite Maps.PMap.gss); *)
        (*       try (rewrite Maps.PMap.gso; et); ss; *)
        (*         try rewrite URA.unit_idl; *)
        (*           try (rewrite Mem.setN_outside; solve_len; try nia); *)
        (*             try eapply PRE; et. *)
        (* replace (strings.length _) with (Z.to_nat z) in * *)
        (*     by now symmetry; apply repeat_length. nia. *) admit "should check". }
      { pose proof (init_data_list_size_pos l).
        i. unfold ClightDmMem0.store_init_data, Mem.store in Heq.
        des_ifs; ss; try rewrite Maps.PMap.gss; try rewrite Mem.setN_outside;
          solve_len; ss; try nia; try (eapply FILLED_ZERO; nia). }
      { admit "should check". }
        (* pose proof (init_data_size_pos a). unfold store_init_data in Heq0. *)
        (* des_ifs; i; do 2 ur; unfold __points_to; des; subst; *)
        (*   try solve [case_points_to; ss; try nia; *)
        (*               try solve [rewrite URA.unit_idl; eapply ORTHO'; et; nia]; *)
        (*                 solve_len; nia]. *)
        (* case_points_to; ss; try nia; try solve [rewrite URA.unit_idl; eapply ORTHO'; et; nia]. *)
        (* replace (strings.length _) with (Z.to_nat z) in l1 by now symmetry; apply repeat_length.  *)
        (* nia. *)
      i. des. splits; et. i. des.
      destruct (Coqlib.zlt ofs (start + init_data_size a)); [|eapply PRE''; nia].
      clear H5.
      admit "".
      (* replace (c b' ofs) with (c0 b' ofs). *)
      (* 2:{ set (start + init_data_size a) as end' in *. clearbody end'. clear - STORE_RSC l0.  *)
      (*   revert_until l. induction l; i; ss; clarify. *)
      (*   des_ifs_safe. pose proof (init_data_size_pos a). *)
      (*   eapply IHl with (ofs:=ofs) in STORE_RSC; try nia. *)
      (*   rewrite <- STORE_RSC. unfold store_init_data in Heq. *)
      (*   des_ifs; do 2 ur; ss; *)
      (*     unfold __points_to; case_points_to; ss; *)
      (*       try rewrite URA.unit_idl; et; nia. } *)
      (* replace (Maps.ZMap.get ofs (Maps.PMap.get b' (Mem.mem_contents m')))  *)
      (*   with (Maps.ZMap.get ofs (Maps.PMap.get b' (Mem.mem_contents m0))). *)
      (* 2:{ set (start + init_data_size a) as end' in *. clearbody end'. clear - STORE_RSC STORE_MEM l0.  *)
      (*   revert_until l. induction l; i; ss; clarify. *)
      (*   des_ifs_safe. pose proof (init_data_size_pos a). *)
      (*   eapply IHl with (ofs:=ofs) in STORE_RSC. *)
      (*   2: et. 2: nia.  *)
      (*   rewrite <- STORE_RSC. unfold ClightlightMem0.store_init_data in Heq. *)
      (*   unfold store_init_data in Heq0. *)
      (*   des_ifs; unfold __points_to in *; do 2 ur; ss; *)
      (*     des_ifs; try rewrite URA.unit_idl; et; *)
      (*       unfold Mem.store in Heq; des_ifs; ss; *)
      (*         rewrite Maps.PMap.gss; rewrite Mem.setN_outside; et. } *)
      (* unfold ClightlightMem0.store_init_data in Heq. *)
      (* unfold store_init_data in Heq0. *)
      (* pose proof (init_data_list_size_pos l). *)
      (* des_ifs; do 2 ur in Heq1; ss; *)
      (*   unfold __points_to in *; case_points_to; ss; *)
      (*     try solve [solve_len; des_ifs; try solve [eapply nth_error_None in Heq0; ss; nia]; *)
      (*                 rewrite ORTHO' in Heq1; try nia; rewrite URA.unit_id in Heq1; clarify]. *)
      (* all: try solve [solve_len; destruct nth_error eqn:X; try solve [eapply nth_error_None in X; ss; nia]; *)
      (*                 rewrite ORTHO' in Heq1; try nia; rewrite URA.unit_id in Heq1; clarify; *)
      (*                 unfold Mem.store in Heq; des_ifs_safe; ss; *)
      (*                 rewrite Maps.PMap.gss; eapply setN_inside in X; solve_len; try nia; et]. *)
      (* + solve_len. destruct nth_error eqn:X; try solve [eapply nth_error_None in X; ss; nia]. *)
      (*   rewrite ORTHO' in Heq1; try nia; rewrite URA.unit_id in Heq1; clarify. *)
      (*   rewrite FILLED_ZERO; try nia.  *)
      (*   rewrite nth_error_repeat in X; try nia; clarify. *)
      (* + rewrite repeat_length in g. nia. *)
  Qed. *)

  (* Lemma sim_cnt_drop_perm m m' res q b lo hi *)
  (*   (PRE: forall ofs, 0 ≤ ofs -> lo ≤ ofs < hi -> *)
  (*                 match res b ofs with *)
  (*                 | Consent.just q mv => mv = Maps.ZMap.get ofs (Maps.PMap.get b (m.(Mem.mem_contents))) *)
  (*                 | _ => False *)
  (*                 end) *)
  (*   (PERM: forall ofs, 0 ≤ ofs -> lo ≤ ofs < hi -> *)
  (*             exists mv, res b ofs = Consent.just q mv) *)
  (*   (DROP: Mem.drop_perm m b lo hi perm = Some m') *)
  (* : *)
  (*   <<PRE': forall ofs, 0 ≤ ofs -> lo ≤ ofs < hi -> *)
  (*               sim_cnt (res b ofs) (Maps.PMap.get b (m'.(Mem.mem_access)) ofs) *)
  (*                 (Maps.ZMap.get ofs (Maps.PMap.get b (m'.(Mem.mem_contents))))>>. *)
  (* Proof. *)
  (*   red. i. hexploit PRE; et. i. des. hexploit PERM; et. i. des. *)
  (*   unfold Mem.drop_perm in DROP. des_ifs_safe. *)
  (*   ss. rewrite Maps.PMap.gss. destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); try nia. *)
  (*   ss. econs; et. *)
  (* Qed. *)

  (* Lemma store_rsc_perm sk res c b' start q l *)
  (*   (STORE_RSC: store_init_data_list sk res b' start perm l = Some c) *)
  (*   (ORTHO: forall b ofs, (b' ≤ b)%positive -> res b ofs = ε) *)
  (* : *)
  (*   <<PERM: forall ofs, 0 ≤ ofs -> start ≤ ofs < start + init_data_list_size l -> *)
  (*             exists mv, c b' ofs = Consent.just q mv>>. *)
  (* Proof. *)
  (*   assert (ORTHO': forall b ofs, ((b' = b /\ start ≤ ofs) \/ (b' < b)%positive) -> res b ofs = ε) *)
  (*     by now i; des; apply ORTHO; nia. *)
  (*   clear ORTHO. *)
  (*   move l at top. revert_until l. induction l; red; i; ss; try nia. des_ifs. *)
  (*   destruct (Coqlib.zle (start + (init_data_size a)) ofs). *)
  (*   - eapply IHl; et; try nia. *)
  (*     i. unfold store_init_data in Heq. *)
  (*     des_ifs; do 2 ur; *)
  (*       unfold __points_to; case_points_to; ss; *)
  (*         try rewrite URA.unit_idl; try (eapply ORTHO'; et); try nia; *)
  (*           solve_len; try nia. *)
  (*     rewrite repeat_length in l2. nia.  *)
  (*   - assert (c b' ofs = c0 b' ofs). *)
  (*     { clear -STORE_RSC g. set (start + _) as end' in *. clearbody end'. *)
  (*       move l at top. revert_until l. induction l; i; ss; clarify. *)
  (*       des_ifs. pose proof (init_data_size_pos a). *)
  (*       eapply IHl with (ofs:=ofs) in STORE_RSC; et; try nia. *)
  (*       rewrite STORE_RSC. unfold store_init_data in Heq. *)
  (*       des_ifs; do 2 ur; *)
  (*         unfold __points_to; case_points_to; ss; try nia; *)
  (*           rewrite URA.unit_idl; et. } *)
  (*     rewrite H3. unfold store_init_data in Heq. *)
  (*       des_ifs; do 2 ur; *)
  (*         unfold __points_to; case_points_to; ss; solve_len; try nia. *)
  (*     all: try destruct nth_error eqn: X; *)
  (*           try solve [eapply nth_error_None in X; ss; nia]; *)
  (*             rewrite ORTHO'; try nia; rewrite URA.unit_id; et. *)
  (*     rewrite repeat_length in g0. nia. *)
  (* Qed. *)

  Local Ltac case_points_to := unfold __points_to; destruct (AList.dec _ _); destruct (Coqlib.zle _ _); destruct (Coqlib.zlt).


  Local Hint Constructors sim_cnt: core.
  Local Hint Constructors sim_allocated: core.
  Local Hint Constructors sim_concrete: core.

  Let world := unit.

  (* iprop -> (if rsc is wf, iprop rsc) *)
  Let wf: world -> Any.t * Any.t -> Prop :=
    mk_wf
      (fun _ _ _mem_tgt0 =>
          ∃ (mem_tgt0: Mem.mem) (memcnt_src0: ClightDmMem1._pointstoRA)
            (memalloc_src0: ClightDmMem1._allocatedRA)
            (memsz_src0: blocksizeRA)
            (memconc_src0: blockaddressRA),

          ⌜(<<TGT: _mem_tgt0 = mem_tgt0↑>>)
          /\ (<<SIM_CNT: forall b ofs (POSOFS: 0 ≤ ofs),
                         sim_cnt (memcnt_src0 b ofs)
                            ((Maps.PMap.get b mem_tgt0.(Mem.mem_access)) ofs)
                            (Maps.ZMap.get ofs (Maps.PMap.get b mem_tgt0.(Mem.mem_contents)))>>)
          /\ (<<SIM_CONC: forall ob,
                          match ob with
                          | Some b => sim_concrete (memconc_src0 (Some b)) (Maps.PTree.get b mem_tgt0.(Mem.mem_concrete))
                          | None => memconc_src0 None = OneShot.white Ptrofs.zero
                          end>>)
          /\ (<<SIM_ALLOC: forall ob,
                           match ob with
                           | Some b => sim_allocated (memalloc_src0 b) (memsz_src0 (Some b))
                                          (Maps.PMap.get b mem_tgt0.(Mem.mem_access)) (Maps.PMap.get b mem_tgt0.(Mem.mem_contents))
                                       /\ ((mem_tgt0.(Mem.nextblock) ≤ b)%positive -> memsz_src0 (Some b) = OneShot.black)
                           | None => memsz_src0 None = OneShot.white 0
                           end>>)⌝
          ** OwnM (Auth.black memcnt_src0)
          ** OwnM (Auth.black memalloc_src0)
          ** OwnM memconc_src0
          ** OwnM memsz_src0)%I
  .

  Local Hint Resolve sim_itree_mon: paco.


  (* Ltac renamer := *)
(*     let tmp := fresh "_tmp_" in *)

(*     match goal with *)
(*     | H: context[OwnM (Auth.black ?x)] |- _ => *)
(*       rename x into tmp; let name := fresh "memk_src0" in rename tmp into name *)
(*     end; *)

(*     match goal with *)
(*     | |- gpaco8 _ _ _ _ _ _ _ _ _ _ _ ((?mp_tgt↑), _) => *)

(*       repeat multimatch mp_tgt with *)
(*              | context[?g] => *)
(*                match (type of g) with *)
(*                | Mem.t => *)
(*                  rename g into tmp; let name := fresh "mem_tgt0" in rename tmp into name *)
(*                | _ => fail *)
(*                end *)
(*              end *)
(*     end *)
(*   . *)

  (* Opaque URA.unit. *)
  (* Arguments URA.car: simpl never. *)
  Local Transparent Mem.alloc Mem.store.

  (* TODO: rollback memory local state formulation *)
  (* TODO: add UB condition in main function invocation *)
  Lemma wf_iff sk : res_init sk = None <-> load_mem sk = None.
  Proof.
  Admitted.

  Lemma init_wf sk m c (RESWF: res_init sk = Some c) (MEMWF: load_mem sk = Some m) :
    wf () (Any.pair ()↑ 
            (c ⋅ GRA.embed (A:=blockaddressRA) (λ ob : option block, 
                                                  match ob with
                                                  | Some _ => OneShot.black
                                                  | None => OneShot.white Ptrofs.zero
                                                  end)
              ⋅ GRA.embed (A:=blocksizeRA) (λ ob : option block,
                                                  match ob with
                                                  | Some b =>
                                                    if Coqlib.plt (Pos.of_succ_nat (List.length sk)) b
                                                    then OneShot.black
                                                    else OneShot.unit
                                                  | None => OneShot.white 0
                                                  end))↑,
            Any.upcast m).
  Proof.
      (* eexists. econs; ss. eapply to_semantic. *)
      (* iIntros "H". iDestruct "H" as "[A B]". iSplits.  *)
      (* iSplitR "B"; [iSplitR "A"; [|iApply "A"]|iApply "B"].  *)
      (* iPureIntro. splits; et. *)
      (* { clear - Σ H H0. unfold load_mem, ClightlightMem0.load_mem. *)
      (*   set sk as sk' at 1 3 5. clearbody sk'. *)
      (*   set ε as res. set Mem.empty as m. *)
      (*   replace xH with (Mem.nextblock m) by ss. *)
      (*   assert (PRE: forall b ofs, 0 <= ofs -> sim_cnt (res b ofs) *)
      (*                 (Maps.PMap.get b (Mem.mem_access m) ofs) *)
      (*                 (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)))) by ss. *)
      (*   assert (ORTHO: forall b ofs, Pos.le (Mem.nextblock m) b -> res b ofs = ε) by ss. *)
      (*   clearbody res m. revert_until sk. induction sk; ss. *)
      (*   unfold alloc_global, ClightlightMem0.alloc_global. *)
      (*   des_ifs; i. *)
      (*   - des_ifs. *)
      (*     + replace (Pos.succ (Mem.nextblock m)) with (Mem.nextblock m0) by now *)
      (*         apply Mem.nextblock_alloc in Heq1; unfold Mem.drop_perm in Heq0; des_ifs. *)
      (*       eapply IHsk; et. *)
      (*       * i. do 2 ur.  *)
      (*         unfold __points_to; case_points_to; ss; try rewrite URA.unit_idl; *)
      (*           try solve [unfold Mem.alloc, Mem.drop_perm in *; *)
      (*                       des_ifs_safe; ss; repeat (rewrite Maps.PMap.gso; et)]; *)
      (*           try (rewrite ORTHO; try nia); try rewrite URA.unit_id; *)
      (*           try (destruct nth_error eqn: X; try solve [eapply nth_error_None in X; ss; nia]); *)
      (*           unfold Mem.alloc, Mem.drop_perm in *; des_ifs_safe; ss; *)
      (*             repeat (rewrite Maps.PMap.gss; destruct (Coqlib.zle _ _); *)
      (*                       destruct (Coqlib.zlt _ _); try nia; ss). *)
      (*           rewrite Maps.PMap.gss. *)
      (*           replace ofs0 with 0 in * by nia. ss. clarify. econs; et. *)
      (*       * i. do 2 ur. apply Mem.nextblock_alloc in Heq1. unfold Mem.drop_perm in Heq0. *)
      (*         des_ifs. ss. rewrite ORTHO; try nia. rewrite URA.unit_id. unfold __points_to. des_ifs; bsimpl. *)
      (*         des. destruct (@dec block positive_Dec b1 (Mem.nextblock m)) in Heq0; clarify. nia. *)
      (*     + exfalso. unfold Mem.alloc in Heq1. clarify. unfold Mem.drop_perm in Heq0. des_ifs_safe. *)
      (*       apply n. unfold Mem.range_perm, Mem.perm. ss. i. rewrite Maps.PMap.gss. *)
      (*       replace ofs0 with 0 in * by nia. ss. econs. *)
      (*   - des_ifs. *)
      (*     + assert (Mem.nextblock m2 = Mem.nextblock m3). *)
      (*       { clear -Heq4. set (gvar_init v) as l in Heq4. set 0 as p in Heq4. clearbody l p. *)
      (*         revert m2 m3 p Heq4. induction l; i; ss; clarify. des_ifs_safe. eapply IHl in Heq4. *)
      (*         unfold ClightlightMem0.store_init_data in Heq.  unfold Mem.store in Heq. *)
      (*         des_ifs. } *)
      (*       replace (Pos.succ (Mem.nextblock m)) with (Mem.nextblock m0). *)
      (*       2:{ apply Mem.nextblock_alloc in Heq2. apply Globalenvs.Genv.store_zeros_nextblock in Heq3. *)
      (*           unfold Mem.drop_perm in Heq1. des_ifs_safe. ss. rewrite <- H2. rewrite Heq3. et. } *)
      (*       eapply IHsk; et; i. *)
      (*       * ss. symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3. *)
      (*         set (gvar_init v) as l in *. clearbody l. *)
      (*         clear IHsk sk Heq s t ofs H1 b H2. *)
      (*         hexploit sim_cnt_alloc; et. i. des. clear PRE ORTHO. *)
      (*         hexploit sim_cnt_store_zero; et; ss. i. des. clear PRE' ORTHO0. *)
      (*         hexploit alloc_store_zero_condition;[|et|];[et|]. i. des. *)
      (*         replace (Mem.nextblock _) with b0 in Heq0 *)
      (*           by now unfold Mem.alloc in Heq2; ss; clarify; ss.  *)
      (*         hexploit sim_cnt_store_initial_data; et. *)
      (*         { i. eapply ORTHO. *)
      (*           assert (Mem.nextblock m1 ≤ Pos.succ b)%positive. *)
      (*           { clear - Heq2 H2. unfold Mem.alloc in Heq2. clarify. ss. nia. } *)
      (*           clear - Heq3 H4. set (init_data_list_size _) as len in *. *)
      (*           clearbody len. remember (Some m2) as optm in *. *)
      (*           move Heq3 at top. revert_until Heq3. *)
      (*           induction Heq3; i; ss; clarify. *)
      (*           eapply IHHeq3; et. unfold Mem.store in e0. ss. des_ifs. } *)
      (*         i. des. hexploit store_rsc_perm; et. *)
      (*         { i. eapply ORTHO. *)
      (*           assert (Mem.nextblock m1 ≤ Pos.succ b)%positive. *)
      (*           { clear - Heq2 H2. unfold Mem.alloc in Heq2. clarify. ss. nia. } *)
      (*           clear - Heq3 H4. set (init_data_list_size _) as len in *. *)
      (*           clearbody len. remember (Some m2) as optm in *. *)
      (*           move Heq3 at top. revert_until Heq3. *)
      (*           induction Heq3; i; ss; clarify. *)
      (*           eapply IHHeq3; et. unfold Mem.store in e0. ss. des_ifs. } *)
      (*         i. des. hexploit sim_cnt_drop_perm; et. i. des. *)
      (*         assert (PRE: forall b ofs,  *)
      (*                   0 ≤ ofs -> not (b = b0 /\ 0 ≤ ofs < 0 + init_data_list_size l) *)
      (*                   -> sim_cnt (c b ofs) (Maps.PMap.get b (Mem.mem_access m0) ofs) *)
      (*                         (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m0)))). *)
      (*         { unfold Mem.drop_perm in Heq1. ss. des_ifs. ss. i. *)
      (*           destruct (Pos.eq_dec b b0); try solve [rewrite Maps.PMap.gso; et]. *)
      (*           subst. rewrite Maps.PMap.gss. *)
      (*           destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); ss; try nia. *)
      (*           eapply PRE'; et. } *)
      (*         clear - PRE H4 H3. *)
      (*         specialize (PRE b1 ofs0 H3). *)
      (*         specialize (H4 ofs0 H3). *)
      (*         set (fun P => P \/ not P) as lem. *)
      (*         assert (lem (b1 = b0 /\ 0 ≤ ofs0 < 0 + init_data_list_size l)) *)
      (*           by now unfold lem; nia. unfold lem in H. *)
      (*         destruct H as [[? ?]| ?]; subst; [eapply H4|eapply PRE]; et. *)
      (*       * assert (Mem.nextblock m3 = Mem.nextblock m0). *)
      (*         { clear -Heq1. unfold Mem.drop_perm in Heq1. des_ifs. } *)
      (*         assert (Mem.nextblock m1 = Mem.nextblock m2). *)
      (*         { clear -Heq3. symmetry in Heq3. *)
      (*           eapply Globalenvs.R_store_zeros_correct in Heq3. *)
      (*           remember (Some m2) as optm. revert m2 Heqoptm. *)
      (*           induction Heq3; i; ss; clarify. *)
      (*           unfold Mem.store in e0. des_ifs. ss. eapply IHHeq3; et. } *)
      (*         rewrite <- H4 in H3. rewrite <- H2 in H3. rewrite <- H5 in H3. *)
      (*         clear - H3 Heq2 ORTHO Heq0. set (gvar_init v) as l in *. clearbody l. *)
      (*         unfold Mem.alloc in Heq2. ss. clarify. ss. set 0 as start in *. *)
      (*         clearbody start.  *)
      (*         assert (ORTHO': forall b ofs, ((Mem.nextblock m = b /\ start ≤ ofs) \/ (Mem.nextblock m < b)%positive) -> res b ofs = Excl.unit) *)
      (*           by now i; des; apply ORTHO; nia. clear ORTHO. *)
      (*         move l at top. revert_until l. *)
      (*         induction l; i; ss; clarify. *)
      (*         { eapply ORTHO'. nia. } *)
      (*         des_ifs_safe. eapply IHl; et. *)
      (*         i. unfold store_init_data in Heq. *)
      (*         des_ifs; do 2 ur;  *)
      (*         unfold __points_to; case_points_to; ss; try nia; *)
      (*         try rewrite URA.unit_idl; try eapply ORTHO'; try nia; cycle 8. *)
      (*         { replace Archi.ptr64 with true in * by refl. nia. } *)
      (*         all: solve_len; destruct nth_error eqn: X; try solve [eapply nth_error_None in X; ss; nia]; try nia. *)
      (*         { rewrite repeat_length in l1. nia. } *)
      (*     + exfalso. unfold Mem.drop_perm in Heq1. des_ifs. eapply n. *)
      (*       assert (Mem.range_perm m0 b0 0 (init_data_list_size (gvar_init v)) Cur Freeable). *)
      (*       { unfold Mem.alloc in Heq2. clarify. unfold Mem.range_perm, Mem.perm. *)
      (*         ss. rewrite Maps.PMap.gss. i. *)
      (*         destruct (Coqlib.zle _ _); destruct (Coqlib.zlt); ss; try nia. econs. } *)
      (*       assert (Mem.range_perm m1 b0 0 (init_data_list_size (gvar_init v)) Cur Freeable). *)
      (*       { clear - Heq3 H2. set (init_data_list_size _) as end' in *. *)
      (*         unfold end' in Heq3. set (init_data_list_size _) as len in Heq3. *)
      (*         set 0 as start in *. unfold start in Heq3. set 0 as start' in Heq3. *)
      (*         assert (start ≤ start') by nia. assert (start' + len ≤ end') by nia. *)
      (*         clearbody end' len start start'. *)
      (*         symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3. *)
      (*         remember (Some m1) as optm in Heq3. *)
      (*         move Heq3 at top. revert_until Heq3.  *)
      (*         induction Heq3; i; ss; clarify. eapply IHHeq3; et; try nia. *)
      (*         unfold Mem.store in e0. des_ifs. } *)
      (*       clear - Heq4 H3. set (gvar_init v) as l in *. *)
      (*       set 0 as start in *. unfold start in Heq4. set 0 as start' in Heq4. *)
      (*       set (init_data_list_size l) as end' in *. *)
      (*       assert (start ≤ start') by nia. *)
      (*       assert (start' + (init_data_list_size l) ≤ end') by nia. *)
      (*       clearbody end' l start start'. *)
      (*       move l at top. revert_until l.  *)
      (*       induction l; i; ss; clarify. des_ifs_safe. *)
      (*       pose proof (init_data_size_pos a). *)
      (*       eapply IHl; et; try nia. *)
      (*       unfold ClightlightMem0.store_init_data, Mem.store in Heq. des_ifs. *)
      (*     + exfalso.  *)
      (*       ss. symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3. *)
      (*       set (gvar_init v) as l in *. clearbody l. *)
      (*       assert (Mem.range_perm m0 b0 0 (init_data_list_size l) Cur Freeable). *)
      (*       { unfold Mem.alloc in Heq2. clarify. unfold Mem.range_perm, Mem.perm. *)
      (*         ss. rewrite Maps.PMap.gss. i. *)
      (*         destruct (Coqlib.zle _ _); destruct (Coqlib.zlt); ss; try nia. econs. } *)
      (*       assert (Mem.range_perm m1 b0 0 (init_data_list_size l) Cur Freeable). *)
      (*       { clear - Heq3 H2. set (init_data_list_size _) as end' in *. *)
      (*         unfold end' in Heq3. set (init_data_list_size _) as len in Heq3. *)
      (*         set 0 as start in *. unfold start in Heq3. set 0 as start' in Heq3. *)
      (*         assert (start ≤ start') by nia. assert (start' + len ≤ end') by nia. *)
      (*         clearbody end' len start start'. *)
      (*         remember (Some m1) as optm in Heq3. *)
      (*         move Heq3 at top. revert_until Heq3.  *)
      (*         induction Heq3; i; ss; clarify. eapply IHHeq3; et; try nia. *)
      (*         unfold Mem.store in e0. des_ifs. } *)
      (*       replace (Mem.nextblock _) with b0 in Heq0 *)
      (*         by now unfold Mem.alloc in Heq2; ss; clarify; ss.  *)
      (*       clear - H3 Heq4 Heq0.  *)
      (*       set 0 as start in *. set (init_data_list_size l) as end' in H3. *)
      (*       set start as start' in Heq0, Heq4. assert (start ≤ start') by nia. *)
      (*       assert (start' + init_data_list_size l ≤ end') by nia. *)
      (*       clearbody start' start end'. move l at top. revert_until l. *)
      (*       induction l; i; ss; clarify. des_ifs. *)
      (*       * pose proof (init_data_size_pos a). *)
      (*         eapply IHl. 1,2: et. *)
      (*         2:{ instantiate (1:=start). nia. } *)
      (*         2:{ instantiate (1:=end'). nia. } *)
      (*         clear - Heq H3. unfold ClightlightMem0.store_init_data, Mem.store in Heq. *)
      (*         unfold Mem.range_perm, Mem.perm in *. i. *)
      (*         des_ifs; ss; eapply H3; try nia. *)
      (*       * clear - Heq1 Heq H3 H H0. pose proof (init_data_list_size_pos l). *)
      (*         unfold ClightlightMem0.store_init_data, Mem.store in Heq. *)
      (*         unfold store_init_data in Heq1. des_ifs; try eapply n; try eapply n0. *)
      (*         all: unfold Mem.valid_access; ss; split; et. *)
      (*         all: unfold Mem.range_perm, Mem.perm, Mem.perm_order' in *; i; *)
      (*               hexploit (H3 ofs); try nia. *)
      (*         7:{ unfold Mptr in *. replace Archi.ptr64 with true in * by refl. ss. nia. } *)
      (*         all: intro X; des_ifs; inv X; econs. *)
      (*     + exfalso. *)
      (*       assert (Mem.range_perm m0 b0 0 (init_data_list_size (gvar_init v)) Cur Freeable). *)
      (*       { unfold Mem.alloc in Heq2. clarify. unfold Mem.range_perm, Mem.perm. *)
      (*         ss. rewrite Maps.PMap.gss. i. *)
      (*         destruct (Coqlib.zle _ _); destruct (Coqlib.zlt); ss; try nia. econs. } *)
      (*       clear - Heq3 H2. set (init_data_list_size _) as end' in *. *)
      (*       unfold end' in Heq3. set (init_data_list_size _) as len in Heq3. *)
      (*       set 0 as start in *. unfold start in Heq3. set 0 as start' in Heq3. *)
      (*       assert (start ≤ start') by nia. assert (start' + len ≤ end') by nia. *)
      (*       clearbody end' len start start'. *)
      (*       symmetry in Heq3. apply Globalenvs.R_store_zeros_correct in Heq3. *)
      (*       remember None as optm in Heq3. *)
      (*       move Heq3 at top. revert_until Heq3.  *)
      (*       induction Heq3; i; ss; clarify. *)
      (*       * eapply IHHeq3 with (start:=start) (end':=end'); et; try nia. *)
      (*         unfold Mem.store in e0. des_ifs. *)
      (*       * unfold Mem.store in e0. des_ifs. apply n0. *)
      (*         econs; ss; try solve [unfold Z.divide; exists p; nia]. *)
      (*         unfold Mem.range_perm, Mem.perm, Mem.perm_order' in *. i. *)
      (*         hexploit H2. { instantiate (1:=ofs). nia. } i. des_ifs. *)
      (*         inv H3; econs. *)
      (*     + exfalso. *)
      (*       replace (Mem.nextblock m) with b0 in * *)
      (*         by now unfold Mem.alloc in Heq2; ss; clarify; ss. *)
      (*       clear - ORTHO Heq0 Heq4. set 0 as start in *. clearbody start. *)
      (*       assert (ORTHO': forall b ofs, ((b0 = b /\ start ≤ ofs) \/ (b0 < b)%positive) -> res b ofs = Excl.unit) *)
      (*         by now i; des; apply ORTHO; nia. clear ORTHO. *)
      (*       set (gvar_init v) as l in *. clearbody l. move l at top. revert_until l. *)
      (*       induction l; i; ss; clarify. des_ifs. *)
      (*       { eapply IHl; et. i. unfold store_init_data in Heq1. *)
      (*         des_ifs; do 2 ur; *)
      (*         unfold __points_to; case_points_to; ss; try nia; *)
      (*         try rewrite URA.unit_idl; try eapply ORTHO'; try nia; cycle 8. *)
      (*         { replace Archi.ptr64 with true in * by refl. nia. } *)
      (*         all: solve_len; destruct nth_error eqn: X; try solve [eapply nth_error_None in X; ss; nia]; try nia. *)
      (*         { rewrite repeat_length in l1. nia. } } *)
      (*       unfold store_init_data, ClightlightMem0.store_init_data in *. *)
      (*       des_ifs; try solve [unfold Mem.store in Heq; des_ifs_safe; *)
      (*                           unfold Mem.valid_access in v0; des; ss]. } *)
      (* i. set ε as r. assert (r b = ε) by ss. rewrite H1. clear H1 r. econs. i. clear -H1. *)
      (* unfold ClightlightMem0.load_mem. set sk as sk' at 1. clearbody sk'. *)
      (* set Mem.empty as m. assert (Maps.PMap.get b (Mem.mem_access m) ofs Cur = None) by ss. *)
      (* clearbody m. revert_until sk. induction sk; i; ss. *)
      (* des_ifs. eapply IHsk; et. unfold ClightlightMem0.alloc_global in Heq. des_ifs. *)
      (* - unfold Mem.alloc in Heq1. unfold Mem.drop_perm in Heq. clarify. des_ifs_safe. ss. *)
      (*   destruct (dec b (Mem.nextblock m)). *)
      (*   + subst. rewrite Maps.PMap.gss. *)
      (*     destruct (Coqlib.zle _ _); try nia. *)
      (*     destruct (Coqlib.zlt _ _); try nia. ss. rewrite Maps.PMap.gss. *)
      (*     destruct (Coqlib.zle _ _); try nia. *)
      (*     destruct (Coqlib.zlt _ _); try nia. ss. *)
      (*   + rewrite Maps.PMap.gso; et. rewrite Maps.PMap.gso; et. *)
      (* - assert (Maps.PMap.get b (Mem.mem_access m1) ofs Cur = None). *)
      (*   { unfold Mem.alloc in Heq1. clarify. ss. *)
      (*     destruct (Pos.eq_dec b (Mem.nextblock m)); *)
      (*       [subst; rewrite Maps.PMap.gss|rewrite Maps.PMap.gso; et]. *)
      (*     destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); ss; try nia. } *)
      (*   assert (Maps.PMap.get b (Mem.mem_access m2) ofs Cur = None). *)
      (*   { clear - H0 H1 Heq2. set 0 as start in Heq2. *)
      (*     assert (0 ≤ start) by nia. set (init_data_list_size _) as len in Heq2. *)
      (*     clearbody start len. symmetry in Heq2. remember (Some m2) as optm in Heq2. *)
      (*     apply Globalenvs.R_store_zeros_correct in Heq2. *)
      (*     move Heq2 at top. revert_until Heq2. *)
      (*     induction Heq2; i; ss; clarify. *)
      (*     eapply IHHeq2; et; try nia. unfold Mem.store in e0. des_ifs. } *)
      (*   assert (Maps.PMap.get b (Mem.mem_access m3) ofs Cur = None). *)
      (*   { clear - H2 H1 Heq3. set 0 as start in Heq3. *)
      (*     assert (0 ≤ start) by nia. set (gvar_init v) as l in Heq3. *)
      (*     clearbody start l. move l at top. revert_until l. *)
      (*     induction l; i; ss; clarify. des_ifs_safe. *)
      (*     pose proof (init_data_size_pos a). *)
      (*     eapply IHl; et; try nia. unfold ClightlightMem0.store_init_data, Mem.store in Heq. *)
      (*     des_ifs. } *)
      (*   clear - H3 H1 Heq. unfold Mem.drop_perm in Heq. des_ifs_safe. ss. *)
      (*   destruct (Pos.eq_dec b b0); *)
      (*     [subst; rewrite Maps.PMap.gss|rewrite Maps.PMap.gso; et]. *)
      (*   destruct (Coqlib.zle _ _); destruct (Coqlib.zlt _ _); ss; try nia. } *)
  Admitted.

  Local Transparent _points_to _allocated_with _has_offset _has_size _has_base.
  Local Transparent Mem.free.

  Lemma sim_salloc :
    sim_fnsem wf top2
      ("salloc", fun_to_tgt "Mem" (to_stb []) (mk_pure salloc_spec))
      ("salloc", cfunU sallocF).
  Proof.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. iIntros "[INV PRE]".
    iDestruct "PRE" as "%"; des; clarify. rename x into sz. unfold inv_with.
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify.

    unfold sallocF. hred_r.
    iApply isim_pget_tgt. hred_r.
    iApply isim_pput_tgt. hred_r.
    iApply isim_apc. iExists None.
    hred_l. iApply isim_choose_src. iExists _.
    iApply isim_upd.

    (* resource formation starts *)
    (* cnt *)
    iOwnWf "CNT" as wfcnt.
    iPoseProof (OwnM_Upd with "CNT") as ">[CNT CNT_POST]".
    { eapply Auth.auth_alloc2.
      instantiate (1:=(__points_to (Mem.nextblock mem_tgt) 0 (repeat (Undef) (Z.to_nat sz)) Q1)).
      do 2 ur. i. ur. specialize (SIM_CNT k k0).
      do 3 ur in wfcnt. des. specialize (wfcnt0 k k0).
      ur in wfcnt0. destruct (Coqlib.zle 0 k0); cycle 1.
      { case_points_to; des_ifs. }
      spc SIM_CNT. inv SIM_CNT; cycle 1.
      { des_ifs; unfold __points_to in *; des_ifs. }
      destruct __points_to eqn: ?; unfold __points_to in *; try solve [des_ifs].
      destruct dec; ss; clarify.
      rewrite mem_tgt.(Mem.nextblock_noaccess) in *; unfold Coqlib.Plt; try nia.
      rewrite Qp_le_lteq in Qwf. des; try spc Qwrite; try spc Qread; des; clarify. }

    (* alloc resource *)
    iOwnWf "ALLOC" as wfalloc.
    iPoseProof (OwnM_Upd with "ALLOC") as ">[ALLOC ALLOC_POST]".
    { eapply Auth.auth_alloc2.
      instantiate (1:=(__allocated_with (Mem.nextblock mem_tgt) Local Q1)).
      do 2 ur. i. specialize (SIM_ALLOC (Some k)). ss. des.
      do 2 ur in wfalloc. des. specialize (wfalloc0 k).
      ur in wfalloc0. inv SIM_ALLOC; cycle 1.
      { des_ifs; unfold __allocated_with in *; des_ifs. }
      destruct __allocated_with eqn: ?; unfold __allocated_with in *; try solve [des_ifs]; cycle 1.
      destruct dec; ss; clarify. hexploit SIM_ALLOC0; try nia.
      i. rewrite SRES in *. clarify. }

    (* size *)
    iOwnWf "SZ" as wfsz.
    iPoseProof (OwnM_Upd with "SZ") as ">[SZ SZ_POST]".
    { instantiate (1:= _has_size (Some (mem_tgt.(Mem.nextblock))) sz).
      instantiate (1:= update memsz_src (Some (mem_tgt.(Mem.nextblock))) (OneShot.white sz)).
      apply URA.pw_updatable. i. ur. unfold update, _has_size.
      destruct dec; clarify; try solve [des_ifs; ur; des_ifs]. 
      destruct dec; clarify. specialize (SIM_ALLOC (Some (mem_tgt.(Mem.nextblock)))).
      ss. des. hexploit SIM_ALLOC0; try nia.
      let X := fresh in intro X; rewrite X.
      etrans; try apply OneShot.oneshot_black_updatable with (a:=sz).
      ur. des_ifs. }

    (* start proving conditions *)
    iModIntro. iApply isim_ret. iModIntro. iSplitR "CNT_POST ALLOC_POST SZ_POST"; cycle 1.
    (* post condition *)
    { iSplit; et.
      set {| blk := Some (mem_tgt.(Mem.nextblock)); sz := sz; SZPOS := fun _ => H5 |} as m.
      iExists m, (Vptr (mem_tgt.(Mem.nextblock)) Ptrofs.zero). 
      iSplits; et.
      unfold m, points_to, has_offset, _points_to, _has_offset; ss.
      iPoseProof (_has_size_dup with "SZ_POST") as "[? SZ_POST]".
      iPoseProof (_has_size_dup with "SZ_POST") as "[? ?]".
      iFrame. iSplits; ss; et; iPureIntro.
      all: rewrite repeat_length; change (Ptrofs.unsigned _) with 0; nia. }
    (* invariant *)
    iExists _. iSplits; ss. iFrame.
    iPureIntro. splits; ss; ss.
    (* sim_cnt *)
    - i. hexploit (SIM_CNT b); et. intro SIM_CNT0.
      destruct (Pos.eq_dec b (mem_tgt.(Mem.nextblock))); clarify; cycle 1.
      { rewrite ! Maps.PMap.gso; et. do 2 ur. case_points_to; ss; rewrite URA.unit_id; et. }
      rewrite ! Maps.PMap.gss. inv SIM_CNT0.
      { rewrite Mem.nextblock_noaccess in PERM; unfold Coqlib.Plt; try nia; clarify. }
      do 2 ur. rewrite <- H7. rewrite URA.unit_idl. rewrite Maps.ZMap.gi.
      case_points_to; ss; cycle 1.
      { rewrite repeat_length in *. destruct Coqlib.zlt; ss. nia. }
      destruct nth_error eqn: ?; cycle 1.
      { rewrite nth_error_None in Heqo. nia. }
      rewrite repeat_length in *. destruct Coqlib.zlt; ss; try nia.
      rewrite repeat_nth in *. des_ifs.
      econs; ss. { econs. } i. econs.
    (* sim_alloc *)
    - i. des_ifs; cycle 1.
      { specialize (SIM_ALLOC None); ss. }
      destruct (Pos.eq_dec b (mem_tgt.(Mem.nextblock))); clarify; cycle 1.
      { specialize (SIM_ALLOC (Some b)); ss; des. rewrite ! Maps.PMap.gso; et. ur.
        unfold __allocated_with. destruct dec; clarify; rewrite URA.unit_id.
        unfold update. des_ifs. split; et. i. apply SIM_ALLOC0; nia. }
      rewrite ! Maps.PMap.gss. specialize (SIM_ALLOC (Some (mem_tgt.(Mem.nextblock)))); ss; des.
      split; i; try nia. hexploit SIM_ALLOC0; try nia. i. rewrite H4 in *. ur.
      inv SIM_ALLOC; clarify. rewrite URA.unit_idl. unfold __allocated_with.
      des_ifs. econs. 7: et. all: et. all: i; clarify.
      { unfold update. des_ifs. }
      { exists Freeable. i. destruct Coqlib.zle; destruct Coqlib.zlt; ss; try nia. split; econs. }
      { destruct Coqlib.zle; destruct Coqlib.zlt; ss; try nia. }
    Unshelve. et.
  Qed.

  Lemma sim_sfree :
    sim_fnsem wf top2
      ("sfree", fun_to_tgt "Mem" (to_stb []) (mk_pure sfree_spec))
      ("sfree", cfunU sfreeF).
  Proof.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. iIntros "[INV PRE]". des_ifs. ss.
    iDestruct "PRE" as "[PRE %]"; clarify.
    do 2 unfold has_offset, _has_offset, points_to, _points_to.
    iDestruct "PRE" as (m mvs vaddr) "[[% P] A]"; des; clarify.
    destruct blk; clarify.
    iDestruct "A" as "[ALLOC_PRE [_ A]]".
    iDestruct "P" as "[_ P]".
    iDestruct "P" as (ofs) "[[[CNT_PRE [SZ_PRE A0]] %] LEN]".
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify.

    unfold sfreeF. hred_r.
    iApply isim_pget_tgt. hred_r.
    (* prove free is safe *)
    unfold Mem.free.
    destruct Mem.range_perm_dec; cycle 1.
    { specialize (SIM_ALLOC (Some b)); ss; des.
      iCombine "ALLOC ALLOC_PRE" as "ALLOC".
      iCombine "SZ SZ_PRE" as "SZ".
      iOwnWf "ALLOC" as wfalloc.
      iOwnWf "SZ" as wfsz. exfalso. apply n.
      unfold _allocated_with in wfalloc. dup wfalloc. apply Auth.auth_included in wfalloc0.
      do 2 red in wfalloc0. des. rewrite <- wfalloc0 in SIM_ALLOC. ur in SIM_ALLOC.
      unfold __allocated_with in SIM_ALLOC. destruct dec; clarify.
      inv SIM_ALLOC; cycle 1.
      { ur in H7; des_ifs. }
      ur in wfalloc. des. ur in wfalloc0. specialize (wfalloc0 b).
      unfold __allocated_with in wfalloc0. destruct dec; clarify.
      destruct ctx; ur in wfalloc0; clarify.
      { des_ifs; apply Qp_not_add_le_l in wfalloc0; clarify. }
      ur in RES. clarify. hexploit COMMON; et. i. clarify.
      hexploit Qfree; et. i. clarify.
      ur in wfsz. specialize (wfsz (Some b)); ss. destruct dec; clarify.
      rewrite SRES in wfsz. ur in wfsz. des_ifs.
      ii. hexploit PERMinrange; et. i. des. unfold Mem.perm, Mem.perm_order'. des_ifs. }
    hred_r.
    iApply isim_pput_tgt. hred_r.
    iApply isim_apc. iExists None.
    hred_l. iApply isim_choose_src. iExists _.
    iApply isim_upd.

    (* resource formation starts *)
    (* cnt *)
    iCombine "CNT CNT_PRE" as "CNT".
    iOwnWf "CNT" as wfcnt.
    iPoseProof (OwnM_Upd with "CNT") as ">CNT".
    { eapply Auth.auth_dealloc.
      instantiate (1:= update memcnt_src b
                        (fun _ofs =>
                          if Coqlib.zle (Ptrofs.unsigned ofs) _ofs && Coqlib.zlt _ofs (Ptrofs.unsigned ofs + length mvs)
                          then Consent.unit
                          else memcnt_src b _ofs)).
      ii. des. rewrite URA.unit_idl. split.
      { do 2 ur in H6. do 2 ur. i. unfold update. destruct dec; et. des_ifs. ur. et. }
      rewrite H7 in *. red. extensionalities. do 2 ur. unfold update. destruct dec; clarify; cycle 1.
      { case_points_to; ss; try rewrite URA.unit_idl; et.
        edestruct nth_error_None. rewrite H11; try nia. }
      case_points_to; ss; try rewrite URA.unit_idl; et.
      do 2 ur in H6. do 2 spc H6. ur in H6.
      destruct ctx; et; try solve [des_ifs]. exfalso.
      unfold __points_to in H6; case_points_to; ss; try nia; des_ifs.
      { apply Qp_not_add_le_l in H6; clarify. }
      { rewrite nth_error_None in Heq. nia. } }

    (* alloc resource *)
    iCombine "ALLOC ALLOC_PRE" as "ALLOC".
    iOwnWf "ALLOC" as wfalloc.
    iPoseProof (OwnM_Upd with "ALLOC") as ">ALLOC".
    { eapply Auth.auth_dealloc.
      instantiate (1:= update memalloc_src b Consent.unit).
      ii. des. rewrite URA.unit_idl. ur in H6. split.
      { ur. i. unfold update. destruct dec; et. ur. et. }
      rewrite H7 in *. red. extensionalities. do 2 ur. unfold update. destruct dec; clarify; cycle 1.
      { unfold __allocated_with. destruct dec; clarify. des_ifs. }
      spc H6. unfold __allocated_with in H6. ur in H6. destruct dec; clarify. ur in H6. des_ifs.
      apply Qp_not_add_le_l in H6. clarify. }

    (* start proving conditions *)
    iModIntro. iApply isim_ret. iModIntro. iSplit; et.
    (* invariant *)
    iExists _. iSplits; ss. iClear "SZ_PRE". iFrame.
    iPureIntro. splits; ss; ss.
    (* sim_cnt *)
    - i. hexploit (SIM_CNT b0); et. intro SIM_CNT0.
      unfold update. destruct dec; clarify; cycle 1.
      { rewrite ! Maps.PMap.gso; et. }
      rewrite ! Maps.PMap.gss.
      do 2 destruct Coqlib.zle; do 2 destruct Coqlib.zlt; ss; try nia.
      rewrite H4 in g. destruct ofs; ss. nia.
    (* sim_alloc *)
    - i. des_ifs; cycle 1.
      { specialize (SIM_ALLOC None); ss. }
      unfold update. destruct dec; clarify; cycle 1.
      { specialize (SIM_ALLOC (Some b0)); ss; des. rewrite ! Maps.PMap.gso; et. }
      rewrite ! Maps.PMap.gss. specialize (SIM_ALLOC (Some b0)); ss; des. et.
    Unshelve. et.
  Qed.

  Lemma sim_load :
    sim_fnsem wf top2
      ("load", fun_to_tgt "Mem" (to_stb []) (mk_pure load_spec))
      ("load", cfunU loadF).
  Proof.
    Local Transparent Mem.load.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. iIntros "[INV PRE]". des_ifs. ss.
    do 2 unfold has_offset, _has_offset, points_to, _points_to.
    iDestruct "PRE" as "[[A P] %]".
    destruct blk; clarify.
    iDestruct "A" as "[% [ALLOC_PRE [SZ1_PRE A]]]".
    iDestruct "P" as "[SZ_PRE P]".
    iDestruct "P" as (ofs) "[[[CNT_PRE [SZ0_PRE A0]] %] LEN]".
    des; clarify. unfold inv_with.
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify.

    unfold loadF. hred_r.
    iApply isim_pget_tgt. hred_r.
    (* if load is safe, the proof is done easily *)
    iAssert ⌜Mem.loadv m0 mem_tgt v = Some (decode_val m0 l)⌝%I as "%"; cycle 1.
    { rewrite H8. hred_r.
      iApply isim_apc. iExists None.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
      { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
      iSplit; ss. iExists _. iFrame. iSplit; ss. iExists _. iFrame. ss. }

    (* offset of points_to and has_offset is equal *)
    iAssert ⌜i = ofs⌝%I as "%".
    { des_ifs; cycle 1. { iDestruct "A" as "%". iDestruct "A0" as "%". des. clarify. }
      iDestruct "A" as (a) "[CONC_PRE %]". iDestruct "A0" as (a0) "[CONC0_PRE %]".
      des; clarify. iCombine "CONC_PRE CONC0_PRE" as "CONC_PRE".
      iPoseProof (_has_base_unique with "CONC_PRE") as "%". subst. et. }
    subst.

    iCombine "CNT CNT_PRE" as "CNT".
    iOwnWf "CNT" as wfcnt.
    ur in wfcnt. rewrite URA.unit_idl in wfcnt. des. apply pw_extends in wfcnt.
    spc wfcnt. apply pw_extends in wfcnt. red in wfcnt. do 2 ur in wfcnt0.

    (* prove safety of load with only sim_cnt *)
    assert (Mem.load m0 mem_tgt b (Ptrofs.unsigned ofs) = Some (decode_val m0 l)).
    - unfold Mem.load. des_ifs; cycle 1.
      { exfalso. apply n. split; cycle 1.
        { etrans; et. destruct m0; ss; solve [exists 1;ss|exists 2;ss|exists 4;ss|exists 8;ss]. } 
        unfold Mem.range_perm. i. spc wfcnt. unfold __points_to in wfcnt.
        case_points_to; ss; try nia; cycle 1.
        { destruct m0; unfold size_chunk_nat in *; ss; nia. }
        destruct nth_error eqn: ?; cycle 1. { rewrite nth_error_None in *. nia. }
        apply Consent.extends in wfcnt; et.
        red in wfcnt. des. do 2 spc SIM_CNT.
        hexploit SIM_CNT. { destruct ofs; ss; nia. }
        i. rewrite wfcnt1 in H10.
        inv H10. clarify. unfold Mem.perm. rewrite PERM. et. }
      do 2 f_equal.
      replace (Mem.getN _ _ _) with l.
      { unfold Mem.decode_normalize. des_ifs.
        { hexploit Mem.decode_normalize_all_fragment; et. i. red in H8.
          unfold Mem.decode_normalize in H8. des_ifs. }
        exfalso. clear - H6 Heq Heq0.
        apply H6. apply proj_determines_decode_val; et. }
      apply nth_error_ext. i.
      destruct (Coqlib.zlt i (size_chunk_nat m0)); cycle 1.
      { edestruct nth_error_None. rewrite H9; try nia.
        edestruct nth_error_None. rewrite H11; et.
        rewrite Mem.getN_length. nia. }
      rewrite nth_error_getN; try nia.
      specialize (wfcnt (Ptrofs.unsigned ofs + i)).
      unfold __points_to in wfcnt.
      case_points_to; ss; try nia.
      destruct nth_error eqn: ?; cycle 1. { rewrite nth_error_None in *. nia. }
      apply Consent.extends in wfcnt; et.
      red in wfcnt. des. spc SIM_CNT.
      specialize (SIM_CNT (Ptrofs.unsigned ofs + i)).
      hexploit SIM_CNT. { destruct ofs; ss; nia. }
      i. rewrite wfcnt1 in H8. inv H8. clarify. rewrite <- Heqo. f_equal. nia.
    (* prove safety of loadv *)
    - unfold Mem.loadv. destruct v; clarify; iDestruct "LEN" as "%"; des; cycle 1.
      (* case: ptr *)
      { iDestruct "A" as "%". iDestruct "A0" as "%". des. clarify. }
      (* case: long *)
      des_ifs_safe.
      iDestruct "A" as (a) "[CONC_PRE %]".
      iDestruct "A0" as (a0) "[CONC0_PRE %]".
      des; clarify.
      iCombine "CONC_PRE CONC0_PRE" as "CONC_PRE".
      iPoseProof (_has_base_unique with "CONC_PRE") as "%". subst.
      iDestruct "CONC_PRE" as "[CONC_PRE _]".
      iCombine "CONC CONC_PRE" as "CONC".
      iOwnWf "CONC" as wfconc.

      (* physical address is larger than base address *)
      ur in wfconc. specialize (wfconc (Some b)). ss. destruct dec; clarify.
      apply OneShot.oneshot_initialized in wfconc. des.
      all: specialize (SIM_CONC (Some b)); ss; rewrite wfconc in SIM_CONC; inv SIM_CONC; clarify.
      replace (Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) base)) with (Ptrofs.unsigned (Ptrofs.repr (Int64.unsigned i - Ptrofs.unsigned base))) in *; cycle 1.
      { unfold Ptrofs.sub, Ptrofs.of_int64. rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)) ; try apply Int64.unsigned_range_2. et. }
      assert (0 ≤ Int64.unsigned i - Ptrofs.unsigned base ≤ Ptrofs.max_unsigned).
      { split; cycle 1. { destruct i; destruct base; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
        destruct (Coqlib.zle 0 (Int64.unsigned i - Ptrofs.unsigned base)); et.
        exfalso. rewrite Ptrofs.unsigned_repr_eq in *.
        replace (Int64.unsigned i - Ptrofs.unsigned base) with (- (Ptrofs.unsigned base - Int64.unsigned i)) in * by nia.
        rewrite Z_mod_nz_opp_full in *; [>rewrite Z.mod_small in *|rewrite Z.mod_small..].
        all: try nia; destruct base; destruct i; ss; try nia.
        change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
      rewrite Ptrofs.unsigned_repr in *; et.

      hexploit wfcnt.
      instantiate (1:= Int64.unsigned i - Ptrofs.unsigned base). intros wfcnt_spc.
      unfold __points_to in wfcnt_spc. case_points_to; ss; try nia; cycle 1.
      { destruct m0; unfold size_chunk_nat in *; ss; nia. }
      destruct nth_error eqn: ?; cycle 1. { rewrite nth_error_None in *. nia. }
      apply Consent.extends in wfcnt_spc; et.
      red in wfcnt_spc. des. hexploit SIM_CNT; et. rewrite wfcnt_spc0. i. inv H19.
      clarify. unfold Mem.denormalize.

      destruct Maps.PTree.select eqn: X; first [apply Maps.PTree.gselectf in X|apply Maps.PTree.gselectnf in X]; des; cycle 1.
      { exfalso. apply X. esplits; et. unfold Mem.denormalize_aux, Mem.addr_is_in_block, Mem.is_valid.
        rewrite <- H18. des_ifs; bsimpl; ss; cycle 1.
        { hexploit mem_tgt.(Mem.access_max). rewrite PERM. rewrite Heq2. i. clarify. }
        change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
        des; try nia. rewrite Pos.ltb_ge in Heq1.
        rewrite Mem.nextblock_noaccess in Heq2; unfold Coqlib.Plt; try nia; clarify. }
      destruct p0. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
      des_ifs; bsimpl; clarify. des.
      hexploit (Mem.no_concrete_overlap mem_tgt (Int64.unsigned i) p0 b).
      { econs; et. nia. }
      { econs; et.
        - hexploit mem_tgt.(Mem.access_max). rewrite PERM. i. red in H19. des_ifs. et.
        - change Ptrofs.modulus with (Ptrofs.max_unsigned + 1). nia. }
      i. subst. rewrite <- H18 in *. clarify.
  Unshelve. all: et.
  Qed.

  Lemma sim_store :
    sim_fnsem wf top2
      ("store", fun_to_tgt "Mem" (to_stb []) (mk_pure store_spec))
      ("store", cfunU storeF).
  Proof.
    Local Transparent Mem.store.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. iIntros "[INV PRE]". des_ifs. ss.
    do 2 unfold has_offset, _has_offset, points_to, _points_to.
    iDestruct "PRE" as "[PRE %]"; clarify.
    iDestruct "PRE" as (mvs_old) "[A P]".
    destruct blk; clarify.
    iDestruct "A" as "[% [ALLOC_PRE [SZ1_PRE A]]]".
    iDestruct "P" as "[SZ_PRE P]".
    iDestruct "P" as (ofs) "[[[CNT_PRE [SZ0_PRE A0]] %] LEN]".
    des; clarify. unfold inv_with.
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify.

    unfold storeF. hred_r.
    iApply isim_pget_tgt. hred_r.

    iAssert ⌜i = ofs⌝%I as "%".
    { des_ifs; cycle 1. { iDestruct "A" as "%". iDestruct "A0" as "%". des. clarify. }
      iDestruct "A" as (a) "[CONC_PRE %]". iDestruct "A0" as (a0) "[CONC0_PRE %]".
      des; clarify. iCombine "CONC_PRE CONC0_PRE" as "CONC_PRE".
      iPoseProof (_has_base_unique with "CONC_PRE") as "%". subst. et. }
    subst.

    iCombine "CNT CNT_PRE" as "CNT".
    iOwnWf "CNT" as wfcnt.
    ur in wfcnt. rewrite URA.unit_idl in wfcnt. des. apply pw_extends in wfcnt.
    spc wfcnt. apply pw_extends in wfcnt. red in wfcnt. do 2 ur in wfcnt0.

    (* check whether it is valid access *)
    assert (Mem.valid_access mem_tgt m0 b (Ptrofs.unsigned ofs) Writable).
    { split; cycle 1.
      { etrans; et. destruct m0; ss; solve [exists 1;ss|exists 2;ss|exists 4;ss|exists 8;ss]. } 
      unfold Mem.range_perm. i. spc wfcnt. unfold __points_to in wfcnt.
      case_points_to; ss; try nia; cycle 1.
      { destruct m0; unfold size_chunk_nat in *; ss; nia. }
      destruct nth_error eqn: ?; cycle 1. { rewrite nth_error_None in *. nia. }
      apply Consent.extends in wfcnt; et.
      red in wfcnt. des. do 2 spc SIM_CNT.
      hexploit SIM_CNT. { destruct ofs; ss; nia. }
      i. rewrite wfcnt1 in H9.
      inv H9. clarify. assert (Q1 = q0) by now eapply antisymmetry; et.
      subst. unfold Mem.perm. rewrite PERM. hexploit Qwrite; et. }

    (* cnt resource formation *)
    iPoseProof (OwnM_Upd with "CNT") as ">[CNT CNT_POST]".
    - eapply Auth.auth_update.
      instantiate (1:= __points_to b (Ptrofs.unsigned ofs) (encode_val m0 v) 1).
      instantiate (1:=update memcnt_src b
                        (fun _ofs =>
                          if Coqlib.zle (Ptrofs.unsigned ofs) _ofs && Coqlib.zlt _ofs (Ptrofs.unsigned ofs + length mvs_old)
                          then
                            match nth_error (encode_val m0 v) (Z.to_nat (_ofs - (Ptrofs.unsigned ofs))) with
                            | Some mv => Consent.just Q1 mv
                            | None => Consent.unit
                            end
                          else memcnt_src b _ofs)).
      ii. des. split.
      { red. do 2 ur. i. unfold update. destruct dec; clarify. des_ifs; clarify; ur; ss. }
      red. extensionalities. rewrite H9. do 2 ur. unfold update.
      destruct dec; clarify; cycle 1.
      { unfold __points_to. destruct dec; clarify. }
      eassert (memcnt_src H10 H11 = _ H10 H11) by now rewrite H9; refl.
      do 2 ur in H12. unfold __points_to in H12. destruct dec; clarify; ss.
      case_points_to; clarify; ss; rewrite encode_val_length in *.
      { destruct nth_error eqn: X; cycle 1. { apply nth_error_None in X. nia. }
        destruct Coqlib.zlt; try nia; ss.
        replace (ctx H10 H11) with (Consent.unit (X:=memval)); [ur; des_ifs|].
        do 2 spc wfcnt0. rewrite H12 in wfcnt0. ur in wfcnt0. des_ifs.
        apply Qp_not_add_le_l in wfcnt0. ss. }
      rewrite URA.unit_idl. destruct Coqlib.zlt; try nia; ss.
      rewrite URA.unit_idl. et. 
    (* storev is safe *)
    - unfold Mem.storev, Mem.store. destruct v0; clarify; iDestruct "LEN" as "%"; des; cycle 1.
      (* case: ptr *)
      + iDestruct "A" as "%". iDestruct "A0" as "%". des. clarify.
        des_ifs. hred_r. iApply isim_pput_tgt. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro.
          splits; et; ss; cycle 1.
          { i. spc SIM_ALLOC. des_ifs. des. split; et.
            destruct (dec b b0); try solve [rewrite Maps.PMap.gso; et].
            subst. rewrite Maps.PMap.gss. inv SIM_ALLOC; et. econs; et. i.
            spc DYNAMIC. des. rewrite Mem.getN_setN_outside; et.
            unfold size_chunk_nat, size_chunk. destruct i; des_ifs; ss; nia. }
          i. unfold update. destruct dec; try solve [rewrite Maps.PMap.gso; et].
          subst. rewrite Maps.PMap.gss. do 3 spc SIM_CNT.
          des_ifs.
          2:{ rewrite nth_error_None in Heq0. rewrite encode_val_length in Heq0.
              destruct m0; unfold size_chunk_nat in *; destruct Coqlib.zlt; ss; nia. }
          2:{ rewrite Mem.setN_outside; et. rewrite encode_val_length.
              bsimpl; des; first [destruct Coqlib.zle|destruct Coqlib.zlt]; ss; try nia. }
          erewrite setN_inside; et; cycle 1.
          { destruct Coqlib.zle; destruct Coqlib.zlt; ss. rewrite encode_val_length. nia. }
          spc wfcnt. unfold __points_to in wfcnt. case_points_to; ss.
          destruct nth_error eqn: ?; cycle 1. { rewrite nth_error_None in Heqo. nia. }
          inv SIM_CNT; [rewrite RES in wfcnt| rewrite <- H12 in wfcnt].
          all: unfold URA.extends in wfcnt; do 2 ur in wfcnt; des; des_ifs; cycle 1.
          econs; et. apply Qp_not_add_le_l in Qwf. ss. }
        iSplit; ss. iExists _. iFrame. iSplit; ss. iExists _. iFrame.
        rewrite encode_val_length. iPureIntro. splits; et; nia.
      (* case: long *)
      + des_ifs_safe.
        iDestruct "A" as (a) "[CONC_PRE %]".
        iDestruct "A0" as (a0) "[CONC0_PRE %]".
        des; clarify.
        iCombine "CONC_PRE CONC0_PRE" as "CONC_PRE".
        iPoseProof (_has_base_unique with "CONC_PRE") as "%". subst.
        iDestruct "CONC_PRE" as "[CONC_PRE _]".
        iCombine "CONC CONC_PRE" as "CONC".
        iOwnWf "CONC" as wfconc.

        (* physical address is larger than base address *)
        ur in wfconc.
        specialize (wfconc (Some b)). ss. destruct dec; clarify.
        apply OneShot.oneshot_initialized in wfconc. des. dup SIM_CONC.
        all: specialize (SIM_CONC (Some b)); ss; rewrite wfconc in SIM_CONC; inv SIM_CONC; clarify.
        replace (Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) base)) with (Ptrofs.unsigned (Ptrofs.repr (Int64.unsigned i - Ptrofs.unsigned base))) in *; cycle 1.
        { unfold Ptrofs.sub, Ptrofs.of_int64. rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)) ; try apply Int64.unsigned_range_2. et. }
        assert (0 ≤ Int64.unsigned i - Ptrofs.unsigned base ≤ Ptrofs.max_unsigned).
        { split; cycle 1. { destruct i; destruct base; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
          destruct (Coqlib.zle 0 (Int64.unsigned i - Ptrofs.unsigned base)); et.
          exfalso. rewrite Ptrofs.unsigned_repr_eq in *.
          replace (Int64.unsigned i - Ptrofs.unsigned base) with (- (Ptrofs.unsigned base - Int64.unsigned i)) in * by nia.
          rewrite Z_mod_nz_opp_full in *; [>rewrite Z.mod_small in *|rewrite Z.mod_small..].
          all: try nia; destruct base; destruct i; ss; try nia.
          change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
        rewrite Ptrofs.unsigned_repr in *; et.

        dup wfcnt. hexploit wfcnt.
        instantiate (1:= Int64.unsigned i - Ptrofs.unsigned base). intros wfcnt_spc.
        unfold __points_to in wfcnt_spc. case_points_to; ss; try nia; cycle 1.
        { destruct m0; unfold size_chunk_nat in *; ss; nia. }
        destruct nth_error eqn: ?; cycle 1. { rewrite nth_error_None in *. nia. }
        apply Consent.extends in wfcnt_spc; et.
        red in wfcnt_spc. des. hexploit SIM_CNT; et. rewrite wfcnt_spc0. i.
        inv H18. clarify. unfold Mem.denormalize.

        destruct Maps.PTree.select eqn: X; first [apply Maps.PTree.gselectf in X|apply Maps.PTree.gselectnf in X]; des; cycle 1.
        { exfalso. apply X. esplits; et. unfold Mem.denormalize_aux, Mem.addr_is_in_block, Mem.is_valid.
          rewrite <- H17. des_ifs; bsimpl; ss; cycle 1.
          { hexploit mem_tgt.(Mem.access_max). rewrite PERM. rewrite Heq2. i. clarify. }
          change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
          des; try nia. rewrite Pos.ltb_ge in Heq1.
          rewrite Mem.nextblock_noaccess in Heq2; unfold Coqlib.Plt; try nia; clarify. }
        destruct p0. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
        rewrite X in X0.
        replace i0 with p0 in * by now des_ifs; bsimpl; clarify.
        replace p0 with b in *; cycle 1.
        { des_ifs; bsimpl; clarify;
          apply (Mem.no_concrete_overlap mem_tgt (Int64.unsigned i)).
          { econs; et.
            - hexploit mem_tgt.(Mem.access_max). rewrite PERM. i. red in H18. des_ifs. et.
            - change Ptrofs.modulus with (Ptrofs.max_unsigned + 1). nia. }
          { econs; et. nia. } }
        rewrite X in *. clarify. des_ifs; bsimpl; clarify. hred_r.
        iApply isim_pput_tgt. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iDestruct "CONC" as "[CONC CONC_PRE]".
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro.
          splits; et; ss; cycle 1.
          { i. spc SIM_ALLOC. des_ifs. des. split; et.
            destruct (dec b b0); try solve [rewrite Maps.PMap.gso; et].
            subst. rewrite Maps.PMap.gss. inv SIM_ALLOC; et. econs; et. i.
            spc DYNAMIC. des. rewrite Mem.getN_setN_outside; et. }
          i. unfold update. destruct dec; try solve [rewrite Maps.PMap.gso; et].
          subst. rewrite Maps.PMap.gss. specialize (SIM_CNT b0 ofs POSOFS).
          des_ifs.
          2:{ rewrite nth_error_None in *. rewrite encode_val_length in *. 
              destruct m0; unfold size_chunk_nat in *; destruct Coqlib.zlt; ss; nia. }
          2:{ rewrite Mem.setN_outside; et. rewrite encode_val_length.
              bsimpl; des; first [destruct Coqlib.zle|destruct Coqlib.zlt]; ss; try nia. }
          erewrite setN_inside; et; cycle 1.
          { destruct Coqlib.zle; destruct Coqlib.zlt; ss. rewrite encode_val_length. nia. }
          specialize (wfcnt ofs). unfold __points_to in wfcnt. case_points_to; ss.
          destruct nth_error eqn: ?; cycle 1. { rewrite nth_error_None in *. nia. }
          inv SIM_CNT; [rewrite RES in *| rewrite <- H18 in *]. 
          all: unfold URA.extends in wfcnt; do 2 ur in wfcnt; des; des_ifs; cycle 1.
          econs; et. apply Qp_not_add_le_l in Qwf0. ss. }
        iSplit; ss. iExists _. iFrame. 
        rewrite _has_base_dup. iDestruct "CONC_PRE" as "[? CONC_PRE]".
        iSplitL "CONC_PRE"; iFrame.
        { iSplit; ss. iExists _. iFrame. ss. }
        iExists (Ptrofs.repr (Int64.unsigned i - Ptrofs.unsigned base)).
        rewrite Ptrofs.unsigned_repr; try nia. iFrame.
        rewrite encode_val_length. iSplits; iFrame; ss; iPureIntro; try nia.
        unfold Ptrofs.sub, Ptrofs.of_int64.
        rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); et.
        destruct i; ss; nia.
  Unshelve. all: et. { apply Eqsth. } { apply Qp_le_po. }
  Qed. 
  
  Lemma paddr_no_overflow_cond i a sz:
        Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) a) ≤ sz ->
        Ptrofs.unsigned a + sz ≤ Ptrofs.max_unsigned ->
        0 ≤ Int64.unsigned i - Ptrofs.unsigned a ≤ sz.
  Proof.
    i. unfold Ptrofs.sub, Ptrofs.of_int64 in *.
    rewrite (Ptrofs.unsigned_repr (_ i)) in H3.
    2:{ apply Int64.unsigned_range_2. }
    rewrite Ptrofs.unsigned_repr_eq in *.
    destruct (Coqlib.zle 0 (Ptrofs.unsigned a - Int64.unsigned i)).
    { destruct (Coqlib.zeq 0 (Int64.unsigned i - Ptrofs.unsigned a)).
      { rewrite <- e in *. ss. }
      replace (Int64.unsigned i - Ptrofs.unsigned a) with (- (Ptrofs.unsigned a - Int64.unsigned i)) in H3 by nia.
      rewrite Z_mod_nz_opp_full in *; [>rewrite Z.mod_small in *|rewrite Z.mod_small..]; et.
      all: try apply Ptrofs.unsigned_range; try nia.
      change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in H3.
      all: destruct a; destruct i; ss; nia. }
    rewrite Z.mod_small in *.
    2:{ destruct a; destruct i; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
    nia.
  Qed.

  Lemma sim_sub_ptr :
    sim_fnsem wf top2
      ("sub_ptr", fun_to_tgt "Mem" (to_stb []) (mk_pure sub_ptr_spec))
      ("sub_ptr", cfunU sub_ptrF).
  Proof.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. iIntros "[INV PRE]". des_ifs. ss.
    do 2 unfold has_offset, _has_offset, points_to, _points_to.
    iDestruct "PRE" as "[[[% A] P] %]"; des; clarify.
    destruct blk; clarify.
    iDestruct "A" as "[ALLOC_PRE [SZ1_PRE A]]".
    iDestruct "P" as "[ALLOC_PRE0 [SZ_PRE P]]".
    unfold inv_with.
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify.

    unfold sub_ptrF. hred_r.
    iApply isim_pget_tgt. hred_r.
    destruct Coqlib.zlt; destruct Coqlib.zle; ss; try nia. hred_r.
    iAssert ⌜Cop._sem_ptr_sub_join_common v0 v mem_tgt = Some (Ptrofs.sub i0 i)⌝%I as "%"; cycle 1.
    { rewrite H4. hred_r.
      iApply isim_apc. iExists None.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
      { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
      iSplit; ss. iFrame. iPureIntro. do 2 f_equal.
      unfold Ptrofs.divs, Ptrofs.sub. f_equal. 
      rewrite (Ptrofs.signed_repr z). 2:{ split; et. change Ptrofs.min_signed with (- Ptrofs.max_signed - 1). nia. }
      f_equal. rewrite Ptrofs.signed_repr; et. }
    destruct v; destruct v0; clarify; des_ifs.
    - ss. des_ifs.
      iDestruct "A" as (a) "[CONC_PRE %]".
      iDestruct "P" as (a0) "[CONC0_PRE %]".
      des; clarify.
      iCombine "CONC_PRE CONC0_PRE" as "CONC_PRE".
      iPoseProof (_has_base_unique with "CONC_PRE") as "%". subst.
      iDestruct "CONC_PRE" as "[CONC_PRE _]".
      iPureIntro. f_equal.
      rewrite !(Ptrofs.sub_add_opp _ a0).
      rewrite Ptrofs.sub_shifted.
      rewrite Ptrofs.sub_add_opp.
      rewrite Int64.sub_add_opp.
      rewrite ptrofs_int64_add; et.
      do 2 f_equal. clear. rewrite ptrofs_int64_neg; et.
      rewrite Ptrofs.to_int64_of_int64; et.
    - iDestruct "A" as "%".
      iDestruct "P" as (a0) "[CONC0_PRE %]".
      des; clarify. ss. unfold Cop._sem_ptr_sub_join. ss.
      iCombine "CONC CONC0_PRE" as "CONC".
      iOwnWf "CONC" as wfconc.
      assert (IntPtrRel.to_int_val mem_tgt (Vptr b i2) = Vlong (Int64.repr (Ptrofs.unsigned a0 + Ptrofs.unsigned i2))).
      { ur in wfconc. specialize (wfconc (Some b)). specialize (SIM_CONC (Some b)).
        ss. destruct dec; clarify.
        apply OneShot.oneshot_initialized in wfconc.
        des; rewrite wfconc in *; inv SIM_CONC; clarify.
        unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. 
        rewrite <- H14. des_ifs. }
      assert (0 ≤ Int64.unsigned i1 - Ptrofs.unsigned a0 ≤ sz m).
      { ii. unfold weak_valid in *. apply paddr_no_overflow_cond; et. }
      assert (Ptrofs.of_int64 (Int64.sub (Int64.repr (Ptrofs.unsigned a0 + Ptrofs.unsigned i2)) i1) = Ptrofs.sub i2 (Ptrofs.sub (Ptrofs.of_int64 i1) a0)).
      { unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub. apply Ptrofs.eqm_samerepr.
        rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)).
        2:{ apply Int64.unsigned_range_2. }
        rewrite (Ptrofs.unsigned_repr (_ - _)).
        2:{ destruct a0; ss; nia. }
        rewrite <- Ptrofs.eqm64; et. apply Int64.eqm_sym.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ eapply Int64.eqm_sub. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        apply Int64.eqm_refl2. nia. }
      rewrite H4. ss. des_ifs_safe. des_ifs; try solve [iPureIntro; f_equal; et].
      { iPureIntro. f_equal. hexploit Ptrofs.eq_spec. rewrite Heq2. i. rewrite H15. et. }
      unfold to_ptr_val, Mem.to_ptr in Heq3. des_ifs. ss. clarify.
      unfold Mem.denormalize in Heq4. apply Maps.PTree.gselectf in Heq4.
      des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq3.
      des_ifs; bsimpl; des; clarify.
      exfalso. hexploit Ptrofs.eq_spec. rewrite Heq2. i. apply H16.
      rewrite H14. f_equal. unfold Ptrofs.sub, Ptrofs.of_int64.
      rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)).
      2:{ apply Int64.unsigned_range_2. }
      ur in wfconc. specialize (wfconc (Some b0)). specialize (SIM_CONC (Some b0)). ss.
      destruct dec; clarify.
      apply OneShot.oneshot_initialized in wfconc. 
      des; rewrite wfconc in *; inv SIM_CONC; clarify.
      rewrite Heq5 in *. clarify.
    - iDestruct "A" as (a) "[CONC_PRE %]".
      iDestruct "P" as "%".
      des; clarify. ss. unfold Cop._sem_ptr_sub_join. ss.
      iCombine "CONC CONC_PRE" as "CONC".
      iOwnWf "CONC" as wfconc.
      assert (IntPtrRel.to_int_val mem_tgt (Vptr b i1) = Vlong (Int64.repr (Ptrofs.unsigned a + Ptrofs.unsigned i1))).
      { ur in wfconc. specialize (wfconc (Some b)). specialize (SIM_CONC (Some b)).
        ss. destruct dec; clarify.
        apply OneShot.oneshot_initialized in wfconc.
        des; rewrite wfconc in *; inv SIM_CONC; clarify.
        unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. 
        rewrite <- H12. des_ifs. }
      assert (0 ≤ Int64.unsigned i2 - Ptrofs.unsigned a ≤ sz m).
      { ii. unfold weak_valid in *. apply paddr_no_overflow_cond; et. } 
      assert (Ptrofs.of_int64 (Int64.sub i2 (Int64.repr (Ptrofs.unsigned a + Ptrofs.unsigned i1))) = Ptrofs.sub (Ptrofs.sub (Ptrofs.of_int64 i2) a) i1).
      { unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub. apply Ptrofs.eqm_samerepr.
        rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)).
        2:{ apply Int64.unsigned_range_2. }
        rewrite (Ptrofs.unsigned_repr (_ - _)).
        2:{ destruct a; ss; nia. }
        rewrite <- Ptrofs.eqm64; et. apply Int64.eqm_sym.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ eapply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_unsigned_repr. }
        apply Int64.eqm_refl2. nia. }
      rewrite H4. unfold to_ptr_val at 2. unfold Cop._sem_ptr_sub.
      ss. des_ifs_safe. des_ifs; try solve [iPureIntro; f_equal; et].
      { iPureIntro. f_equal. hexploit Ptrofs.eq_spec. rewrite Heq2. i. rewrite H15. et. }
      unfold to_ptr_val, Mem.to_ptr in Heq3. des_ifs. ss. clarify.
      unfold Mem.denormalize in Heq4. apply Maps.PTree.gselectf in Heq4.
      des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq3.
      des_ifs; bsimpl; des; clarify.
      exfalso. hexploit Ptrofs.eq_spec. rewrite Heq2. i. apply H16.
      rewrite H12. f_equal. unfold Ptrofs.sub, Ptrofs.of_int64.
      rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)).
      2:{ apply Int64.unsigned_range_2. }
      ur in wfconc. specialize (wfconc (Some b)). specialize (SIM_CONC (Some b)). ss.
      destruct dec; clarify.
      apply OneShot.oneshot_initialized in wfconc. 
      des; rewrite wfconc in *; inv SIM_CONC; clarify.
      rewrite Heq5 in *. clarify.
    - iDestruct "P" as "%".
      iDestruct "A" as "%".
      des. clarify. ss. des_ifs.
    Unshelve. et.
  Qed.

  Lemma weak_valid_nil_paddr_base a sz :
    Ptrofs.unsigned (Ptrofs.repr (- Ptrofs.unsigned a)) ≤ sz ->
    Ptrofs.unsigned a <> 0 ->
    Ptrofs.unsigned a + sz ≤ Ptrofs.max_unsigned -> False.
  Proof.
    unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.of_int64 _)) with 0%Z.
    rewrite Ptrofs.unsigned_repr_eq. i.
    rewrite Z_mod_nz_opp_full in *.
    2:{ rewrite Z.mod_small; et. destruct a; ss; nia. }
    rewrite Z.mod_small in *. 2:{ destruct a; ss; nia. }
    change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
    nia.
  Qed.

  Lemma paddr_no_overflow_cond_lt i a sz:
        Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) a) < sz ->
        Ptrofs.unsigned a + sz ≤ Ptrofs.max_unsigned ->
        0 ≤ Int64.unsigned i - Ptrofs.unsigned a < sz.
  Proof.
    i. unfold Ptrofs.sub, Ptrofs.of_int64 in *.
    rewrite (Ptrofs.unsigned_repr (_ i)) in H3.
    2:{ apply Int64.unsigned_range_2. }
    rewrite Ptrofs.unsigned_repr_eq in *.
    destruct (Coqlib.zle 0 (Ptrofs.unsigned a - Int64.unsigned i)).
    { destruct (Coqlib.zeq 0 (Int64.unsigned i - Ptrofs.unsigned a)).
      { rewrite <- e in *. ss. }
      replace (Int64.unsigned i - Ptrofs.unsigned a) with (- (Ptrofs.unsigned a - Int64.unsigned i)) in H3 by nia.
      rewrite Z_mod_nz_opp_full in *; [>rewrite Z.mod_small in *|rewrite Z.mod_small..]; et.
      all: try apply Ptrofs.unsigned_range; try nia.
      change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in H3.
      all: destruct a; destruct i; ss; nia. }
    rewrite Z.mod_small in *.
    2:{ destruct a; destruct i; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
    nia.
  Qed.

  Lemma sim_cmp_ptr :
    sim_fnsem wf top2
      ("cmp_ptr", fun_to_tgt "Mem" (to_stb []) (mk_pure cmp_ptr_spec))
      ("cmp_ptr", cfunU cmp_ptrF).
  Proof.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. unfold "@".
    iIntros "[INV PRE]".
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify. unfold cmp_ptrF. do 8 (try destruct x as [?|x]).
    - ss. iDestruct "PRE" as "%". des. clarify. hred_r.
      iApply isim_pget_tgt. hred_r. destruct Vnullptr eqn:?; clarify.
      rewrite <- Heqv. unfold cmp_ptr. des_ifs_safe.
      unfold Val.cmplu_bool. destruct Vnullptr eqn:?; clarify.
      hred_r. 
      iApply isim_apc. iExists None.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
      { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
      iSplit; ss. iPureIntro. unfold Vnullptr in Heqv0. des_ifs. 
    - unfold cmp_ptr_hoare1. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[[% P] %]".
      do 2 unfold has_offset, _has_offset.
      destruct blk eqn:?; clarify.
      iDestruct "P" as "[ALLOC_PRE0 [SZ_PRE P]]".
      des; clarify. hred_r.
      iApply isim_pget_tgt. hred_r. destruct Vnullptr eqn:?; clarify.
      destruct v; clarify; des_ifs_safe.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        unfold cmp_ptr. des_ifs_safe. ss. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. destruct (Int64.eq i0 i1) eqn: ?.
        { apply Int64.same_if_eq in Heqb0. subst. 
          unfold Vnullptr in Heqv0. des_ifs. exfalso.
          eapply weak_valid_nil_paddr_base; et. }
        iSplit; ss. iExists _. iFrame. iPureIntro. splits; ss.
      + iDestruct "P" as "%". des. clarify.
        unfold cmp_ptr. des_ifs_safe. unfold Vnullptr in Heqv0. clarify.
        rewrite Int64.eq_true. ss. des_ifs_safe. rewrite Int64.eq_true. ss.
        iCombine "ALLOC ALLOC_PRE0" as "ALLOC".
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz. dup SIM_ALLOC.
        ur in wfalloc. des. rewrite URA.unit_idl in wfalloc.
        ur in wfalloc0. apply pw_extends in wfalloc. spc wfalloc.
        ur in wfsz. specialize (wfsz (Some b)). specialize (SIM_ALLOC (Some b)).
        unfold __allocated_with in *. ss.
        destruct dec; clarify. apply Consent.extends in wfalloc; et. red in wfalloc. des.
        rewrite wfalloc1 in *. apply OneShot.oneshot_initialized in wfsz.
        des; rewrite wfsz in *; inv SIM_ALLOC; clarify.
        unfold weak_valid in *. destruct m. ss. rewrite Heqo in *.
        hexploit SZPOS; et. i.
        assert (Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1)
                || Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1 - 1) = true).
        { bsimpl. unfold Mem.valid_pointer.
          do 2 destruct Mem.perm_dec; ss; et.
          exfalso. dup PERMinrange.
          specialize (PERMinrange (Ptrofs.unsigned i1)).
          specialize (PERMinrange0 (Ptrofs.unsigned i1 - 1)).
          unfold size_chunk in *. des_ifs.
          assert (init ≤ 0) by now destruct tag; try solve [hexploit COMMON; et; nia|hexploit DYNAMIC; et; des; nia].
          unfold Mem.perm in *.
          assert (init ≤ Ptrofs.unsigned i1 < sz \/ init ≤ Ptrofs.unsigned i1 - 1 < sz) by now destruct i1; ss; nia.
          destruct H7.
          { spc PERMinrange. des. rewrite PERMinrange in *. apply n. econs. }
          { spc PERMinrange0. des. rewrite PERMinrange0 in *. apply n0. econs. } }
        rewrite H6. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iDestruct "ALLOC" as "[ALLOC ?]".
        iDestruct "SZ" as "[SZ ?]".
        iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. ss. 
    - unfold cmp_ptr_hoare2. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[[% P] %]".
      do 2 unfold has_offset, _has_offset.
      destruct blk eqn:?; clarify.
      iDestruct "P" as "[ALLOC_PRE0 [SZ_PRE P]]".
      des; clarify. hred_r.
      iApply isim_pget_tgt. hred_r. destruct Vnullptr eqn:?; clarify.
      destruct v; clarify; des_ifs_safe.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        unfold cmp_ptr. des_ifs_safe. ss. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. destruct (Int64.eq i0 i1) eqn: ?.
        { apply Int64.same_if_eq in Heqb0. subst. 
          unfold Vnullptr in Heqv0. des_ifs.
          unfold Ptrofs.sub in H5. change (Ptrofs.unsigned (Ptrofs.of_int64 _)) with 0%Z in H5.
          exfalso. eapply weak_valid_nil_paddr_base; et. }
        iSplit; ss. iExists _. iFrame. iPureIntro. splits; ss.
      + iDestruct "P" as "%". des. clarify.
        unfold cmp_ptr. des_ifs_safe. unfold Vnullptr in Heqv0. clarify.
        rewrite Int64.eq_true. ss. des_ifs_safe. rewrite Int64.eq_true. ss.
        iCombine "ALLOC ALLOC_PRE0" as "ALLOC".
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz. dup SIM_ALLOC.
        ur in wfalloc. des. rewrite URA.unit_idl in wfalloc.
        ur in wfalloc0. apply pw_extends in wfalloc. spc wfalloc.
        ur in wfsz. specialize (wfsz (Some b)). specialize (SIM_ALLOC (Some b)).
        unfold __allocated_with in *. ss.
        destruct dec; clarify. apply Consent.extends in wfalloc; et. red in wfalloc. des.
        rewrite wfalloc1 in *. apply OneShot.oneshot_initialized in wfsz.
        des; rewrite wfsz in *; inv SIM_ALLOC; clarify.
        unfold weak_valid in *. destruct m. ss. rewrite Heqo in *.
        hexploit SZPOS; et. i.
        assert (Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1)
                || Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1 - 1) = true).
        { bsimpl. unfold Mem.valid_pointer.
          do 2 destruct Mem.perm_dec; ss; et.
          exfalso. dup PERMinrange.
          specialize (PERMinrange (Ptrofs.unsigned i1)).
          specialize (PERMinrange0 (Ptrofs.unsigned i1 - 1)).
          unfold size_chunk in *. des_ifs.
          assert (init ≤ 0) by now destruct tag; try solve [hexploit COMMON; et; nia|hexploit DYNAMIC; et; des; nia].
          unfold Mem.perm in *.
          assert (init ≤ Ptrofs.unsigned i1 < sz \/ init ≤ Ptrofs.unsigned i1 - 1 < sz) by now destruct i1; ss; nia.
          destruct H7.
          { spc PERMinrange. des. rewrite PERMinrange in *. apply n. econs. }
          { spc PERMinrange0. des. rewrite PERMinrange0 in *. apply n0. econs. } }
        rewrite H6. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iDestruct "ALLOC" as "[ALLOC ?]".
        iDestruct "SZ" as "[SZ ?]".
        iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. ss. 
    - unfold cmp_ptr_hoare3. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[[% P] %]".
      do 2 unfold has_offset, _has_offset.
      destruct blk eqn:?; clarify.
      iDestruct "P" as "[ALLOC_PRE0 [SZ_PRE P]]".
      des; clarify. hred_r.
      iApply isim_pget_tgt. hred_r. destruct Vnullptr eqn:?; clarify.
      destruct v; clarify; des_ifs_safe.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        unfold cmp_ptr. des_ifs_safe. ss. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. destruct (Int64.eq i1 i0) eqn: ?.
        { apply Int64.same_if_eq in Heqb0. subst. 
          unfold Vnullptr in Heqv0. des_ifs.
          unfold Ptrofs.sub in H5. change (Ptrofs.unsigned (Ptrofs.of_int64 _)) with 0%Z in H5.
          exfalso. eapply weak_valid_nil_paddr_base; et. }
        iSplit; ss. iExists _. iFrame. iPureIntro. splits; ss.
      + iDestruct "P" as "%". des. clarify.
        unfold cmp_ptr. des_ifs_safe. unfold Vnullptr in Heqv0. clarify.
        rewrite Int64.eq_true. ss. des_ifs_safe. rewrite Int64.eq_true. ss.
        iCombine "ALLOC ALLOC_PRE0" as "ALLOC".
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz. dup SIM_ALLOC.
        ur in wfalloc. des. rewrite URA.unit_idl in wfalloc.
        ur in wfalloc0. apply pw_extends in wfalloc. spc wfalloc.
        ur in wfsz. specialize (wfsz (Some b)). specialize (SIM_ALLOC (Some b)).
        unfold __allocated_with in *. ss.
        destruct dec; clarify. apply Consent.extends in wfalloc; et. red in wfalloc. des.
        rewrite wfalloc1 in *. apply OneShot.oneshot_initialized in wfsz.
        des; rewrite wfsz in *; inv SIM_ALLOC; clarify.
        unfold weak_valid in *. destruct m. ss. rewrite Heqo in *.
        hexploit SZPOS; et. i.
        assert (Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1)
                || Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1 - 1) = true).
        { bsimpl. unfold Mem.valid_pointer.
          do 2 destruct Mem.perm_dec; ss; et.
          exfalso. dup PERMinrange.
          specialize (PERMinrange (Ptrofs.unsigned i1)).
          specialize (PERMinrange0 (Ptrofs.unsigned i1 - 1)).
          unfold size_chunk in *. des_ifs.
          assert (init ≤ 0) by now destruct tag; try solve [hexploit COMMON; et; nia|hexploit DYNAMIC; et; des; nia].
          unfold Mem.perm in *.
          assert (init ≤ Ptrofs.unsigned i1 < sz \/ init ≤ Ptrofs.unsigned i1 - 1 < sz) by now destruct i1; ss; nia.
          destruct H7.
          { spc PERMinrange. des. rewrite PERMinrange in *. apply n. econs. }
          { spc PERMinrange0. des. rewrite PERMinrange0 in *. apply n0. econs. } }
        rewrite H6. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iDestruct "ALLOC" as "[ALLOC ?]".
        iDestruct "SZ" as "[SZ ?]".
        iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. ss. 
    - unfold cmp_ptr_hoare4. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[[% P] %]".
      do 2 unfold has_offset, _has_offset.
      destruct blk eqn:?; clarify.
      iDestruct "P" as "[ALLOC_PRE0 [SZ_PRE P]]".
      des; clarify. hred_r.
      iApply isim_pget_tgt. hred_r. destruct Vnullptr eqn:?; clarify.
      destruct v; clarify; des_ifs_safe.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        unfold cmp_ptr. des_ifs_safe. ss. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. destruct (Int64.eq i1 i0) eqn: ?.
        { apply Int64.same_if_eq in Heqb0. subst. 
          unfold Vnullptr in Heqv0. des_ifs.
          unfold Ptrofs.sub in H5. change (Ptrofs.unsigned (Ptrofs.of_int64 _)) with 0%Z in H5.
          exfalso. eapply weak_valid_nil_paddr_base; et. }
        iSplit; ss. iExists _. iFrame. iPureIntro. splits; ss.
      + iDestruct "P" as "%". des. clarify.
        unfold cmp_ptr. des_ifs_safe. unfold Vnullptr in Heqv0. clarify.
        rewrite Int64.eq_true. ss. des_ifs_safe. rewrite Int64.eq_true. ss.
        iCombine "ALLOC ALLOC_PRE0" as "ALLOC".
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz. dup SIM_ALLOC.
        ur in wfalloc. des. rewrite URA.unit_idl in wfalloc.
        ur in wfalloc0. apply pw_extends in wfalloc. spc wfalloc.
        ur in wfsz. specialize (wfsz (Some b)). specialize (SIM_ALLOC (Some b)).
        unfold __allocated_with in *. ss.
        destruct dec; clarify. apply Consent.extends in wfalloc; et. red in wfalloc. des.
        rewrite wfalloc1 in *. apply OneShot.oneshot_initialized in wfsz.
        des; rewrite wfsz in *; inv SIM_ALLOC; clarify.
        unfold weak_valid in *. destruct m. ss. rewrite Heqo in *.
        hexploit SZPOS; et. i.
        assert (Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1)
                || Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1 - 1) = true).
        { bsimpl. unfold Mem.valid_pointer.
          do 2 destruct Mem.perm_dec; ss; et.
          exfalso. dup PERMinrange.
          specialize (PERMinrange (Ptrofs.unsigned i1)).
          specialize (PERMinrange0 (Ptrofs.unsigned i1 - 1)).
          unfold size_chunk in *. des_ifs.
          assert (init ≤ 0) by now destruct tag; try solve [hexploit COMMON; et; nia|hexploit DYNAMIC; et; des; nia].
          unfold Mem.perm in *.
          assert (init ≤ Ptrofs.unsigned i1 < sz \/ init ≤ Ptrofs.unsigned i1 - 1 < sz) by now destruct i1; ss; nia.
          destruct H7.
          { spc PERMinrange. des. rewrite PERMinrange in *. apply n. econs. }
          { spc PERMinrange0. des. rewrite PERMinrange0 in *. apply n0. econs. } }
        rewrite H6. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iDestruct "ALLOC" as "[ALLOC ?]".
        iDestruct "SZ" as "[SZ ?]".
        iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. ss. 
    (* non-trivial cases *)
    - unfold cmp_ptr_hoare5. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[[[% P] A] %]".
      do 2 unfold has_offset, _has_offset.
      destruct blk eqn:?; clarify.
      iDestruct "P" as "[ALLOC_PRE [SZ_PRE P]]".
      iDestruct "A" as "[ALLOC0_PRE [SZ0_PRE A]]".
      des; clarify. hred_r.
      iApply isim_pget_tgt. hred_r.
      destruct v0; clarify; des_ifs_safe;
      destruct v; clarify; des_ifs_safe.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        iDestruct "A" as (a0) "[CONC0_PRE %]". des. clarify.
        unfold cmp_ptr. unfold Val.cmplu_bool. des_ifs_safe.
        hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame.
        iCombine "CONC_PRE CONC0_PRE" as "CONC_PRE".
        iPoseProof (_has_base_unique with "CONC_PRE") as "%".
        subst. iDestruct "CONC_PRE" as "[CONC_PRE ?]".
        iSplitR "CONC_PRE"; cycle 1.
        { iExists _. iFrame. ss. }
        iSplit; cycle 1.
        { iExists _. iFrame. ss. } 
        unfold cmp_ofs. unfold Int64.cmpu.
        hexploit paddr_no_overflow_cond; et.
        hexploit (paddr_no_overflow_cond i1); et. i.
        replace (Ptrofs.unsigned _) with (Int64.unsigned i1 - Ptrofs.unsigned a0).
        2:{ unfold Ptrofs.sub, Ptrofs.of_int64.
            rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); try apply Int64.unsigned_range_2.
            rewrite Ptrofs.unsigned_repr; et. destruct i1; destruct a0; ss; nia. }
        replace (Ptrofs.unsigned (Ptrofs.sub _ _)) with (Int64.unsigned i2 - Ptrofs.unsigned a0).
        2:{ unfold Ptrofs.sub, Ptrofs.of_int64.
            rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); try apply Int64.unsigned_range_2.
            rewrite Ptrofs.unsigned_repr; et. destruct i2; destruct a0; ss; nia. }
        des_ifs; iPureIntro; f_equal.
        * pose proof (Int64.eq_spec i1 i2).
          destruct (Int64.eq i1 i2) eqn:?.
          { subst. symmetry. rewrite Z.eqb_eq. et. }
          symmetry. rewrite Z.eqb_neq. ii. apply H12.
          apply Int64.same_if_eq. unfold Int64.eq. destruct Coqlib.zeq; nia.
        * f_equal. pose proof (Int64.eq_spec i1 i2).
          destruct (Int64.eq i1 i2) eqn:?.
          { subst. symmetry. rewrite Z.eqb_eq. et. }
          symmetry. rewrite Z.eqb_neq. ii. apply H12.
          apply Int64.same_if_eq. unfold Int64.eq. destruct Coqlib.zeq; nia.
        * unfold Int64.ltu. destruct Coqlib.zlt; clarify.
          { symmetry. rewrite Z.ltb_lt. nia. }
          symmetry. rewrite Z.ltb_ge. nia.
        * unfold Int64.ltu. destruct Coqlib.zlt; clarify.
          { ss. symmetry. rewrite Z.leb_gt. nia. }
          symmetry. rewrite Z.leb_le. nia.
        * unfold Int64.ltu. rewrite Z.gtb_ltb. destruct Coqlib.zlt; clarify.
          { symmetry. rewrite Z.ltb_lt. nia. }
          symmetry. rewrite Z.ltb_ge. nia.
        * unfold Int64.ltu. rewrite Z.geb_leb. destruct Coqlib.zlt; clarify.
          { ss. symmetry. rewrite Z.leb_gt. nia. }
          ss. symmetry. rewrite Z.leb_le. nia.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        iDestruct "A" as "%". des. clarify.
        iCombine "ALLOC ALLOC_PRE" as "ALLOC".
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz. dup SIM_ALLOC.
        ur in wfalloc. des. rewrite URA.unit_idl in wfalloc.
        ur in wfalloc0. apply pw_extends in wfalloc. spc wfalloc.
        ur in wfsz. specialize (wfsz (Some b)). specialize (SIM_ALLOC (Some b)).
        unfold __allocated_with in *. ss.
        destruct dec; clarify. apply Consent.extends in wfalloc; et. red in wfalloc. des.
        rewrite wfalloc1 in *. apply OneShot.oneshot_initialized in wfsz.
        des; rewrite wfsz in *; inv SIM_ALLOC; clarify.
        unfold weak_valid in *. destruct m. ss. rewrite Heqo in *.
        hexploit SZPOS; et. i.
        pose proof (Int64.eq_spec i1 Int64.zero).
        destruct (Int64.eq i1 Int64.zero) eqn: ?.
        { subst. exfalso. eapply weak_valid_nil_paddr_base; et. }
        unfold cmp_ptr_join. ss.
        iCombine "CONC CONC_PRE" as "CONC".
        iOwnWf "CONC" as wfconc.
        assert (IntPtrRel.to_int_val mem_tgt (Vptr b i2) = Vlong (Int64.repr (Ptrofs.unsigned a + Ptrofs.unsigned i2))).
        { ur in wfconc. specialize (wfconc (Some b)). specialize (SIM_CONC (Some b)).
          ss. destruct dec; clarify.
          apply OneShot.oneshot_initialized in wfconc.
          des; rewrite wfconc in *; inv SIM_CONC; clarify.
          unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. 
          rewrite <- H12. des_ifs. }
        hexploit paddr_no_overflow_cond; et. i.
        rewrite H10. unfold to_ptr_val at 2. unfold to_int_val. ss.
        unfold cmp_ptr. unfold Val.cmplu_bool at 1. des_ifs_safe. hred_r.
        des_ifs; hred_r.
        * apply eqb_prop in Heq2. subst.
          iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "ALLOC" as "[ALLOC ?]".
          iDestruct "SZ" as "[SZ ?]".
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iSplit; ss.
          2:{ iExists _. iFrame. ss. }
          iPureIntro. f_equal. unfold cmp_ofs, Int64.cmpu.
          replace (Ptrofs.unsigned (Ptrofs.sub _ _)) with (Int64.unsigned i1 - Ptrofs.unsigned a).
          2:{ unfold Ptrofs.sub, Ptrofs.of_int64.
              rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); try apply Int64.unsigned_range_2.
              rewrite Ptrofs.unsigned_repr; et. destruct i1; destruct a; ss; nia. }
          unfold Int64.eq, Int64.ltu.
          rewrite Int64.unsigned_repr.
          2:{ change Int64.max_unsigned with Ptrofs.max_unsigned. split; try nia.
              destruct a; destruct i2; ss; nia. }
          des_ifs; try nia.
        * apply eqb_false_iff in Heq2.
          unfold Val.cmplu_bool in *. unfold to_ptr_val in *.
          des_ifs.
          { unfold Mem.to_ptr in *. des_ifs. }
          { unfold Mem.to_ptr in *. des_ifs.
            unfold Mem.denormalize in *.
            apply Maps.PTree.gselectf in Heq1. des.
            unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
            des_ifs; ss; clarify; bsimpl; clarify.
            ur in wfconc. specialize (wfconc (Some b)). ss. destruct dec; clarify.
            apply OneShot.oneshot_initialized in wfconc.
            specialize (SIM_CONC (Some b)). ss.
            destruct wfconc as [wfconc|wfconc]; rewrite wfconc in SIM_CONC; inv SIM_CONC; clarify.
            rewrite Heq7 in H15; clarify. exfalso.
            apply Heq2. unfold Ptrofs.cmpu, Int64.cmpu.
            unfold Ptrofs.eq, Ptrofs.ltu, Int64.eq, Int64.ltu.
            change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
            rewrite Ptrofs.unsigned_repr; try nia.
            rewrite Int64.unsigned_repr.
            2:{ change Int64.max_unsigned with Ptrofs.max_unsigned.
                destruct base; destruct i2; ss; nia. }
            des_ifs; nia. }
          { unfold Mem.to_ptr in *. des_ifs.
            unfold Mem.denormalize in *.
            apply Maps.PTree.gselectf in Heq6. des.
            unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
            des_ifs; ss; clarify; bsimpl; clarify. des.
            assert (i1 = Int64.repr (Ptrofs.unsigned a + Ptrofs.unsigned i2)).
            { apply Int64.same_if_eq. destruct c; ss; clarify.
              all: destruct (Int64.eq i1 (Int64.repr _)); clarify. }
            subst. rewrite Int64.unsigned_repr in *.
            all: try (change Int64.max_unsigned with Ptrofs.max_unsigned; destruct a; destruct i2; ss; nia).
            ur in wfconc. specialize (wfconc (Some b)). ss. destruct dec; clarify.
            apply OneShot.oneshot_initialized in wfconc.
            specialize (SIM_CONC (Some b)). ss.
            destruct wfconc as [wfconc|wfconc]; rewrite wfconc in SIM_CONC; inv SIM_CONC; clarify.
            pose proof (mem_tgt.(Mem.no_concrete_overlap) (Ptrofs.unsigned base + Ptrofs.unsigned i2)).
            red in H13. hexploit (H13 b b1); i; clarify.
            { destruct base; destruct i2; ss. econs; et; try nia. 
              specialize (PERMinrange (intval + intval0 - intval)).
              unfold Mem.valid_pointer in *.
              do 2 destruct (Mem.perm_dec ); clarify.
              unfold Mem.perm in *.
              replace (intval + intval0 - intval) with intval0 by nia.
              unfold Mem.perm_order' in *. des_ifs.
              pose proof (mem_tgt.(Mem.access_max) b intval0).
              rewrite Heq11 in H14. unfold Mem.perm_order'' in *. des_ifs.
              et. }
            { econs; et. rewrite Z.ltb_lt in *. rewrite Z.leb_le in *. nia. } }
        * iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "ALLOC" as "[ALLOC ?]".
          iDestruct "SZ" as "[SZ ?]".
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iSplit; ss.
          2:{ iExists _. iFrame. ss. }
          iPureIntro. f_equal. unfold cmp_ofs, Int64.cmpu.
          replace (Ptrofs.unsigned (Ptrofs.sub _ _)) with (Int64.unsigned i1 - Ptrofs.unsigned a).
          2:{ unfold Ptrofs.sub, Ptrofs.of_int64.
              rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); try apply Int64.unsigned_range_2.
              rewrite Ptrofs.unsigned_repr; et. destruct i1; destruct a; ss; nia. }
          unfold Int64.eq, Int64.ltu.
          rewrite Int64.unsigned_repr.
          2:{ change Int64.max_unsigned with Ptrofs.max_unsigned. split; try nia.
              destruct a; destruct i2; ss; nia. }
          des_ifs; try nia.
      + iDestruct "P" as "%". des. clarify.
        iDestruct "A" as (a) "[CONC_PRE %]". des. clarify.
        rename i1 into i0. rename i2 into i1. rename i0 into i2.
        iCombine "ALLOC ALLOC_PRE" as "ALLOC".
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz. dup SIM_ALLOC.
        ur in wfalloc. des. rewrite URA.unit_idl in wfalloc.
        ur in wfalloc0. apply pw_extends in wfalloc. spc wfalloc.
        ur in wfsz. specialize (wfsz (Some b)). specialize (SIM_ALLOC (Some b)).
        unfold __allocated_with in *. ss.
        destruct dec; clarify. apply Consent.extends in wfalloc; et. red in wfalloc. des.
        rewrite wfalloc1 in *. apply OneShot.oneshot_initialized in wfsz.
        des; rewrite wfsz in *; inv SIM_ALLOC; clarify.
        unfold weak_valid in *. destruct m. ss. rewrite Heqo in *.
        hexploit SZPOS; et. i.
        pose proof (Int64.eq_spec i1 Int64.zero).
        destruct (Int64.eq i1 Int64.zero) eqn: ?.
        { subst. exfalso. apply H7.
          unfold weak_valid, Ptrofs.sub, Ptrofs.of_int64 in *.
          change (Ptrofs.unsigned (Ptrofs.repr (Int64.unsigned _))) with 0 in *.
          rewrite Ptrofs.unsigned_repr_eq in *.
          rewrite Z_mod_nz_opp_full in *; [>rewrite Z.mod_small in *|rewrite Z.mod_small..]; et.
          all: try apply Ptrofs.unsigned_range.
          change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
        unfold cmp_ptr_join. ss.
        iCombine "CONC CONC_PRE" as "CONC".
        iOwnWf "CONC" as wfconc.
        assert (IntPtrRel.to_int_val mem_tgt (Vptr b i2) = Vlong (Int64.repr (Ptrofs.unsigned a + Ptrofs.unsigned i2))).
        { ur in wfconc. specialize (wfconc (Some b)). specialize (SIM_CONC (Some b)).
          ss. destruct dec; clarify.
          apply OneShot.oneshot_initialized in wfconc.
          des; rewrite wfconc in *; inv SIM_CONC; clarify.
          unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. 
          rewrite <- H12. des_ifs. }
        hexploit paddr_no_overflow_cond; et. i.
        rewrite H10. unfold to_ptr_val at 1. unfold to_int_val. ss.
        unfold cmp_ptr. unfold Val.cmplu_bool at 1. des_ifs_safe.
        Local Opaque Val.cmplu_bool. hred_r.
        des_ifs; hred_r.
        Local Transparent Val.cmplu_bool.
        * apply eqb_prop in Heq2. rewrite Heq2.
          iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "ALLOC" as "[ALLOC ?]".
          iDestruct "SZ" as "[SZ ?]".
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iSplit; ss.
          2:{ iExists _. iFrame. ss. }
          iPureIntro. f_equal. unfold cmp_ofs, Int64.cmpu.
          replace (Ptrofs.unsigned (Ptrofs.sub _ _)) with (Int64.unsigned i1 - Ptrofs.unsigned a).
          2:{ unfold Ptrofs.sub, Ptrofs.of_int64.
              rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); try apply Int64.unsigned_range_2.
              rewrite Ptrofs.unsigned_repr; et. destruct i1; destruct a; ss; nia. }
          unfold Int64.eq, Int64.ltu.
          rewrite Int64.unsigned_repr.
          2:{ change Int64.max_unsigned with Ptrofs.max_unsigned. split; try nia.
              destruct a; destruct i2; ss; nia. }
          des_ifs; try nia.
        * apply eqb_false_iff in Heq2.
          unfold Val.cmplu_bool in *. unfold to_ptr_val in *.
          des_ifs.
          { unfold Mem.to_ptr in *. des_ifs. }
          { unfold Mem.to_ptr in *. des_ifs.
            unfold Mem.denormalize in *.
            apply Maps.PTree.gselectf in Heq1. des.
            unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
            des_ifs; ss; clarify; bsimpl; clarify.
            ur in wfconc. specialize (wfconc (Some b1)). ss. destruct dec; clarify.
            apply OneShot.oneshot_initialized in wfconc.
            specialize (SIM_CONC (Some b1)). ss.
            destruct wfconc as [wfconc|wfconc]; rewrite wfconc in SIM_CONC; inv SIM_CONC; clarify.
            rewrite Heq7 in H15; clarify. exfalso.
            apply Heq2. unfold Ptrofs.cmpu, Int64.cmpu.
            unfold Ptrofs.eq, Ptrofs.ltu, Int64.eq, Int64.ltu.
            change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
            rewrite Ptrofs.unsigned_repr; try nia.
            rewrite Int64.unsigned_repr.
            2:{ change Int64.max_unsigned with Ptrofs.max_unsigned.
                destruct base; destruct i2; ss; nia. }
            des_ifs; nia. }
          { unfold Mem.to_ptr in *. des_ifs.
            unfold Mem.denormalize in *.
            apply Maps.PTree.gselectf in Heq6. des.
            unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
            des_ifs; ss; clarify; bsimpl; clarify. des.
            assert (Int64.repr (Ptrofs.unsigned a + Ptrofs.unsigned i2) = i1).
            { apply Int64.same_if_eq. destruct c; ss; clarify.
              all: destruct (Int64.eq (Int64.repr _) i1); clarify. }
            subst. rewrite Int64.unsigned_repr in *.
            all: try (change Int64.max_unsigned with Ptrofs.max_unsigned; destruct a; destruct i2; ss; nia).
            ur in wfconc. specialize (wfconc (Some b)). ss. destruct dec; clarify.
            apply OneShot.oneshot_initialized in wfconc.
            specialize (SIM_CONC (Some b)). ss.
            destruct wfconc as [wfconc|wfconc]; rewrite wfconc in SIM_CONC; inv SIM_CONC; clarify.
            pose proof (mem_tgt.(Mem.no_concrete_overlap) (Ptrofs.unsigned base + Ptrofs.unsigned i2)).
            red in H13. hexploit (H13 b b1); i; clarify.
            { destruct base; destruct i2; ss. econs; et; try nia. 
              specialize (PERMinrange (intval + intval0 - intval)).
              unfold Mem.valid_pointer in *.
              do 2 destruct (Mem.perm_dec ); clarify.
              unfold Mem.perm in *.
              replace (intval + intval0 - intval) with intval0 by nia.
              unfold Mem.perm_order' in *. des_ifs.
              pose proof (mem_tgt.(Mem.access_max) b intval0).
              rewrite Heq12 in H14. unfold Mem.perm_order'' in *. des_ifs.
              et. }
            { econs; et. rewrite Z.ltb_lt in *. rewrite Z.leb_le in *. nia. } }
        * iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "ALLOC" as "[ALLOC ?]".
          iDestruct "SZ" as "[SZ ?]".
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iSplit; ss.
          2:{ iExists _. iFrame. ss. }
          iPureIntro. f_equal. unfold cmp_ofs, Int64.cmpu.
          replace (Ptrofs.unsigned (Ptrofs.sub _ _)) with (Int64.unsigned i1 - Ptrofs.unsigned a).
          2:{ unfold Ptrofs.sub, Ptrofs.of_int64.
              rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); try apply Int64.unsigned_range_2.
              rewrite Ptrofs.unsigned_repr; et. destruct i1; destruct a; ss; nia. }
          unfold Int64.eq, Int64.ltu.
          rewrite Int64.unsigned_repr.
          2:{ change Int64.max_unsigned with Ptrofs.max_unsigned. split; try nia.
              destruct a; destruct i2; ss; nia. }
          des_ifs; try nia.
      + iDestruct "P" as "%". des. clarify.
        iDestruct "A" as "%". des. clarify.
        unfold cmp_ptr. des_ifs_safe. unfold Val.cmplu_bool.
        des_ifs_safe. unfold weak_valid in *.
        destruct m. ss. rewrite Heqo in *. hexploit SZPOS; et. i.
        iCombine "ALLOC ALLOC_PRE" as "ALLOC". 
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz.
        ur in wfalloc. ur in wfsz. rewrite URA.unit_idl in wfalloc. des.
        apply pw_extends in wfalloc. red in wfalloc. spc wfalloc. dup SIM_ALLOC.
        specialize (wfsz (Some b)). ss. unfold __allocated_with in *.
        destruct dec; clarify. ur in wfalloc0. apply Consent.extends in wfalloc; et.
        red in wfalloc. des. specialize (SIM_ALLOC (Some b)). ss. des.
        rewrite wfalloc1 in *. apply OneShot.oneshot_initialized in wfsz.
        des; rewrite wfsz in *; inv SIM_ALLOC; clarify.
        assert ((Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1)
                || Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1 - 1)) = true).
        { bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          destruct (Coqlib.zeq (Ptrofs.unsigned i1) sz0); subst.
          { unfold size_chunk in *. des_ifs. destruct i1; ss.
            hexploit (PERMinrange (intval - 1)).
            { destruct tag; try solve [hexploit COMMON; et; nia| hexploit DYNAMIC; et; des; nia]. }
            i. des. unfold Mem.perm, Mem.perm_order' in *.
            rewrite H7 in *. apply n0. econs. }
          { unfold size_chunk in *. des_ifs. destruct i1; ss.
            hexploit (PERMinrange intval).
            { destruct tag; try solve [hexploit COMMON; et; nia| hexploit DYNAMIC; et; des; nia]. }
            i. des. unfold Mem.perm, Mem.perm_order' in *.
            rewrite H7 in *. apply n. econs. } }
        assert ((Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i2)
                || Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i2 - 1)) = true).
        { clear H7. bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          destruct (Coqlib.zeq (Ptrofs.unsigned i2) sz0); subst.
          { unfold size_chunk in *. des_ifs. destruct i2; ss.
            hexploit (PERMinrange (intval - 1)).
            { destruct tag; try solve [hexploit COMMON; et; nia| hexploit DYNAMIC; et; des; nia]. }
            i. des. unfold Mem.perm, Mem.perm_order' in *.
            rewrite H7 in *. apply n0. econs. }
          { unfold size_chunk in *. des_ifs. destruct i2; ss.
            hexploit (PERMinrange intval).
            { destruct tag; try solve [hexploit COMMON; et; nia| hexploit DYNAMIC; et; des; nia]. }
            i. des. unfold Mem.perm, Mem.perm_order' in *.
            rewrite H7 in *. apply n. econs. } }
        rewrite H7. rewrite H8. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iDestruct "ALLOC" as "[ALLOC ALLOC_PRE]".
        iDestruct "SZ" as "[SZ SZ_PRE]".
        iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. iSplit; ss. iSplit; ss. 
        iPureIntro. f_equal. unfold cmp_ofs, Ptrofs.cmpu.
        unfold Ptrofs.eq, Ptrofs.ltu.
        des_ifs; nia.
    - unfold cmp_ptr_hoare6. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[[[% P] A] %]".
      do 2 unfold has_offset, _has_offset.
      destruct (blk m) eqn:?; clarify.
      iDestruct "A" as "[ALLOC_PRE [SZ_PRE A]]".
      destruct (blk m0) eqn:?; clarify.
      iDestruct "P" as "[ALLOC0_PRE [SZ0_PRE P]]".
      des; clarify. hred_r.
      iApply isim_pget_tgt. hred_r.
      destruct v0; clarify; des_ifs_safe;
      destruct v; clarify; des_ifs_safe.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        iDestruct "A" as (a0) "[CONC0_PRE %]". des. clarify.
        unfold cmp_ptr. unfold Val.cmplu_bool. des_ifs_safe. hred_r.
        iCombine "ALLOC ALLOC_PRE" as "ALLOC". 
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz.
        iDestruct "ALLOC" as "[ALLOC ALLOC_PRE]".
        iDestruct "SZ" as "[SZ SZ_PRE]".
        iCombine "ALLOC ALLOC0_PRE" as "ALLOC". 
        iCombine "SZ SZ0_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc0.
        iOwnWf "SZ" as wfsz0.
        iDestruct "ALLOC" as "[ALLOC ALLOC0_PRE]".
        iDestruct "SZ" as "[SZ SZ0_PRE]".
        ur in wfalloc. ur in wfsz. rewrite URA.unit_idl in wfalloc. des.
        apply pw_extends in wfalloc. red in wfalloc.
        ur in wfalloc0. ur in wfsz0. rewrite URA.unit_idl in wfalloc0. des.
        apply pw_extends in wfalloc0. red in wfalloc0. ur in wfalloc1.
        specialize (wfsz (Some b)).
        specialize (wfsz0 (Some b0)).
        specialize (wfalloc b).
        specialize (wfalloc0 b0).
        hexploit (SIM_ALLOC (Some b)).
        hexploit (SIM_ALLOC (Some b0)).
        i. des. unfold __allocated_with in *. destruct dec; clarify.
        destruct dec; clarify.
        apply Consent.extends in wfalloc; et. red in wfalloc. des. rewrite wfalloc3 in *.
        apply Consent.extends in wfalloc0; et. red in wfalloc0. des. rewrite wfalloc4 in *.
        apply OneShot.oneshot_initialized in wfsz.
        apply OneShot.oneshot_initialized in wfsz0.
        destruct wfsz as [wfsz|wfsz]; rewrite wfsz in H12; inv H12; clarify.
        destruct wfsz0 as [wfsz0|wfsz0]; rewrite wfsz0 in H4; inv H4; clarify.
        iCombine "CONC CONC_PRE" as "CONC". 
        iOwnWf "CONC" as wfconc.
        iDestruct "CONC" as "[CONC CONC_PRE]".
        iCombine "CONC CONC0_PRE" as "CONC". 
        iOwnWf "CONC" as wfconc0.
        iDestruct "CONC" as "[CONC CONC0_PRE]".
        ur in wfconc. specialize (wfconc (Some b0)).
        ur in wfconc0. specialize (wfconc0 (Some b)).
        ss. destruct dec; clarify. destruct dec; clarify.
        apply OneShot.oneshot_initialized in wfconc.
        apply OneShot.oneshot_initialized in wfconc0.
        hexploit (SIM_CONC (Some b)). i. 
        hexploit (SIM_CONC (Some b0)). i.
        destruct wfconc as [wfconc|wfconc]; rewrite wfconc in H12; inv H12; clarify.
        destruct wfconc0 as [wfconc0|wfconc0]; rewrite wfconc0 in H4; inv H4; clarify.

        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. iSplitL "CONC_PRE"; cycle 1.
        { iExists _. iFrame. ss. }
        iSplit; ss. 2:{ iExists _. iFrame. ss. }
        iPureIntro. f_equal. pose proof (Int64.eq_spec i2 i1).
        destruct (Int64.eq i2 i1); et. subst. exfalso.
        hexploit paddr_no_overflow_cond_lt; et. i.
        unfold size_chunk in *. des_ifs.
        hexploit (paddr_no_overflow_cond_lt i1 base); et. i.
        assert (init ≤ 0) by now destruct tag; try solve [hexploit COMMON; et; nia|hexploit DYNAMIC; et; des; nia].
        hexploit (PERMinrange (Int64.unsigned i1 - Ptrofs.unsigned base0)); try nia.
        assert (init0 ≤ 0) by now destruct tag0; try solve [hexploit COMMON0; et; nia|hexploit DYNAMIC0; et; des; nia].
        hexploit (PERMinrange0 (Int64.unsigned i1 - Ptrofs.unsigned base)); try nia.
        i. des. pose proof (mem_tgt.(Mem.no_concrete_overlap) (Int64.unsigned i1)).
        red in H25. hexploit (H25 b b0).
        { econs; et.
          - pose proof (mem_tgt.(Mem.access_max) b (Int64.unsigned i1 - Ptrofs.unsigned base0)).
            rewrite H20 in H26. unfold Mem.perm_order'' in *. des_ifs. et.
          - destruct base0; destruct i1; ss.
            change Int64.modulus with (Ptrofs.max_unsigned + 1) in *.
            change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
        { econs; et.
          - pose proof (mem_tgt.(Mem.access_max) b0 (Int64.unsigned i1 - Ptrofs.unsigned base)).
            rewrite H19 in H26. unfold Mem.perm_order'' in *. des_ifs. et.
          - destruct base; destruct i1; ss.
            change Int64.modulus with (Ptrofs.max_unsigned + 1) in *.
            change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
        i. unfold "#^" in *. subst. rewrite <- Heqo in Heqo0. clarify.
      + iDestruct "P" as "%". des. clarify.
        iDestruct "A" as (a) "[CONC_PRE %]". des. clarify.
        iCombine "ALLOC ALLOC_PRE" as "ALLOC". 
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz.
        iDestruct "ALLOC" as "[ALLOC ALLOC_PRE]".
        iDestruct "SZ" as "[SZ SZ_PRE]".
        iCombine "ALLOC ALLOC0_PRE" as "ALLOC". 
        iCombine "SZ SZ0_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc0.
        iOwnWf "SZ" as wfsz0.
        iDestruct "ALLOC" as "[ALLOC ALLOC0_PRE]".
        iDestruct "SZ" as "[SZ SZ0_PRE]".
        ur in wfalloc. ur in wfsz. rewrite URA.unit_idl in wfalloc. des.
        apply pw_extends in wfalloc. red in wfalloc.
        ur in wfalloc0. ur in wfsz0. rewrite URA.unit_idl in wfalloc0. des.
        apply pw_extends in wfalloc0. red in wfalloc0. ur in wfalloc1.
        specialize (wfsz (Some b)).
        specialize (wfsz0 (Some b0)).
        specialize (wfalloc b).
        specialize (wfalloc0 b0).
        hexploit (SIM_ALLOC (Some b)).
        hexploit (SIM_ALLOC (Some b0)).

        i. des. unfold __allocated_with in *. destruct dec; clarify.
        destruct dec; clarify.
        apply Consent.extends in wfalloc; et. red in wfalloc. des. rewrite wfalloc3 in *.
        apply Consent.extends in wfalloc0; et. red in wfalloc0. des. rewrite wfalloc4 in *.
        apply OneShot.oneshot_initialized in wfsz.
        apply OneShot.oneshot_initialized in wfsz0.
        destruct wfsz as [wfsz|wfsz]; rewrite wfsz in H10; inv H10; clarify.
        destruct wfsz0 as [wfsz0|wfsz0]; rewrite wfsz0 in H4; inv H4; clarify.
        destruct m, m0. unfold "#^", valid in *. ss. rewrite Heqo in *. rewrite Heqo0 in *.
        hexploit SZPOS; et. i.
        hexploit SZPOS0; et. i.
        pose proof (Int64.eq_spec i1 Int64.zero).
        destruct (Int64.eq i1 Int64.zero) eqn: ?.
        { subst. exfalso. 
          unfold weak_valid, Ptrofs.sub, Ptrofs.of_int64 in *.
          change (Ptrofs.unsigned (Ptrofs.repr (Int64.unsigned _))) with 0 in *.
          change (0 - Ptrofs.unsigned a) with (- Ptrofs.unsigned a) in *.
          eapply weak_valid_nil_paddr_base; et. nia. }
        unfold cmp_ptr_join. ss.
        iCombine "CONC CONC_PRE" as "CONC".
        iOwnWf "CONC" as wfconc.
        ur in wfconc. specialize (wfconc (Some b)). ss. destruct dec; clarify.
        hexploit (SIM_CONC (Some b)). i.
        apply OneShot.oneshot_initialized in wfconc. 
        des; rewrite wfconc in *; inv H14; clarify.
        hexploit paddr_no_overflow_cond_lt; et. i.
        assert (to_ptr_val mem_tgt (Vlong i1) = Vptr b (Ptrofs.repr (Int64.unsigned i1 - Ptrofs.unsigned base))).
        { unfold to_ptr_val, Mem.to_ptr.
          des_ifs; [apply Maps.PTree.gselectf in Heq1|apply Maps.PTree.gselectnf in Heq1]; des.
          - ss. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
            des_ifs; bsimpl; des; clarify.
            hexploit (PERMinrange (Int64.unsigned i1 - Ptrofs.unsigned base)).
            { unfold size_chunk in *. des_ifs. destruct tag; (hexploit COMMON + hexploit DYNAMIC); et; nia. }
            i. des. 
            pose proof (mem_tgt.(Mem.no_concrete_overlap) (Int64.unsigned i1)).
            red in H19. hexploit (H19 b b1).
            { econs; et.
              - epose proof (mem_tgt.(Mem.access_max) b _).
                rewrite H16 in H20. unfold Mem.perm_order'' in *. des_ifs. et.
              - destruct base; destruct i1; ss.
                change Int64.modulus with (Ptrofs.max_unsigned + 1) in *.
                change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
            { econs; et. destruct i1; ss. nia. }
            i. subst. rewrite Heq3 in *. clarify.
          - exfalso. apply Heq1. esplits; et. unfold Mem.denormalize_aux.
            rewrite <- H17. unfold size_chunk in *. des_ifs. bsimpl.
            hexploit (PERMinrange (Int64.unsigned i1 - Ptrofs.unsigned base)); try solve [destruct tag; (hexploit COMMON + hexploit DYNAMIC); et; nia].
            i. unfold Mem.is_valid, Mem.addr_is_in_block in *. rewrite <- H17 in Heq2. des.
            { hexploit (mem_tgt.(Mem.nextblock_noaccess) b); try solve [rewrite H13; et].
              apply Pos.ltb_ge in Heq2. unfold Coqlib.Plt. nia. rewrite H16. et. }
            { des_ifs; bsimpl; des.
              { rewrite PERMoutrange in H16; clarify. destruct tag; (hexploit COMMON + hexploit DYNAMIC); et; nia. }
              { destruct i1; destruct base; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
              { hexploit (mem_tgt.(Mem.access_max)). rewrite Heq4. rewrite H16. i. inv H19. } } }
        rewrite H15. unfold to_ptr_val at 1. unfold to_int_val at 2. ss.
        unfold cmp_ptr. des_ifs_safe. unfold Val.cmplu_bool at 2.
        rewrite Ptrofs.unsigned_repr; [|destruct base; ss; nia].
        assert (Mem.valid_pointer mem_tgt b0 (Ptrofs.unsigned i2) = true).
        { bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          unfold size_chunk in *. des_ifs. destruct i2; ss.
          hexploit (PERMinrange0 intval).
          { destruct tag0; try solve [hexploit COMMON0; et; nia| hexploit DYNAMIC0; et; des; nia]. }
          i. des. unfold Mem.perm, Mem.perm_order' in *.
          rewrite H16 in *. apply n. econs. }
        assert (Mem.valid_pointer mem_tgt b (Int64.unsigned i1 - Ptrofs.unsigned base) = true).
        { clear H16. bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          unfold size_chunk in *. des_ifs. destruct i1; destruct base; ss.
          hexploit (PERMinrange (intval - intval0)).
          { destruct tag; try solve [hexploit COMMON; et; nia| hexploit DYNAMIC; et; des; nia]. }
          i. des. unfold Mem.perm, Mem.perm_order' in *.
          rewrite H16 in *. apply n. econs. }
        rewrite H18. rewrite H16. ss. destruct eq_block; clarify.
        Local Opaque Val.cmplu_bool.
        des_ifs; hred_r; des_ifs; hred_r.
        Local Transparent Val.cmplu_bool.
        * iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iExists _. iFrame. ss.
        * unfold Val.cmplu_bool, to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
          des_ifs. ss. clarify. hexploit Int64.eq_spec. rewrite H20.
          i. subst. unfold Mem.valid_pointer in *.
          do 2 destruct Mem.perm_dec; ss; clarify.
          unfold Mem.perm, Mem.perm_order' in *. des_ifs.
          hexploit (mem_tgt.(Mem.weak_valid_address_range) b0); et.
          { apply Ptrofs.unsigned_range. }
          { unfold Mem._weak_valid_pointer, Mem._valid_pointer.
            pose proof (mem_tgt.(Mem.access_max) b0 (Ptrofs.unsigned i2)).
            rewrite Heq4 in H19. unfold Mem.perm_order'' in *.
            des_ifs. rewrite Heq6. left. econs. }
          i. inv H19; ss.
          rewrite Int64.unsigned_repr in *.
          2,3,4: change Int64.max_unsigned with (Ptrofs.modulus - 1); nia.
          pose proof (mem_tgt.(Mem.no_concrete_overlap) (z0 + Ptrofs.unsigned i2)).
          red in H19. hexploit (H19 b b0).
          { econs; et.
            - pose proof (mem_tgt.(Mem.access_max) b (z0 + Ptrofs.unsigned i2 - Ptrofs.unsigned base)).
              rewrite Heq2 in H21. unfold Mem.perm_order'' in *. des_ifs. et.
            - destruct base; destruct i2; ss.
              change Int64.modulus with (Ptrofs.max_unsigned + 1) in *.
              change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
          { econs; et.
            - pose proof (mem_tgt.(Mem.access_max) b0 (Ptrofs.unsigned i2)).
              rewrite Heq4 in H21. unfold Mem.perm_order'' in *. des_ifs.
              replace (_ + _ - _) with (Ptrofs.unsigned i2) by nia. et.
            - destruct i2; ss. nia. }
        i. clarify.
        * iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iExists _. iFrame. ss.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        iDestruct "A" as "%". des. clarify.
        iCombine "ALLOC ALLOC_PRE" as "ALLOC". 
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz.
        iDestruct "ALLOC" as "[ALLOC ALLOC_PRE]".
        iDestruct "SZ" as "[SZ SZ_PRE]".
        iCombine "ALLOC ALLOC0_PRE" as "ALLOC". 
        iCombine "SZ SZ0_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc0.
        iOwnWf "SZ" as wfsz0.
        iDestruct "ALLOC" as "[ALLOC ALLOC0_PRE]".
        iDestruct "SZ" as "[SZ SZ0_PRE]".
        ur in wfalloc. ur in wfsz. rewrite URA.unit_idl in wfalloc. des.
        apply pw_extends in wfalloc. red in wfalloc.
        ur in wfalloc0. ur in wfsz0. rewrite URA.unit_idl in wfalloc0. des.
        apply pw_extends in wfalloc0. red in wfalloc0. ur in wfalloc1.
        specialize (wfsz (Some b)).
        specialize (wfsz0 (Some b0)).
        specialize (wfalloc b).
        specialize (wfalloc0 b0).
        hexploit (SIM_ALLOC (Some b)).
        hexploit (SIM_ALLOC (Some b0)).

        i. des. unfold __allocated_with in *. destruct dec; clarify.
        destruct dec; clarify.
        apply Consent.extends in wfalloc; et. red in wfalloc. des. rewrite wfalloc3 in *.
        apply Consent.extends in wfalloc0; et. red in wfalloc0. des. rewrite wfalloc4 in *.
        apply OneShot.oneshot_initialized in wfsz.
        apply OneShot.oneshot_initialized in wfsz0.
        destruct wfsz as [wfsz|wfsz]; rewrite wfsz in H10; inv H10; clarify.
        destruct wfsz0 as [wfsz0|wfsz0]; rewrite wfsz0 in H4; inv H4; clarify.
        destruct m, m0. unfold "#^", valid in *. ss. rewrite Heqo in *. rewrite Heqo0 in *.
        hexploit SZPOS; et. i.
        hexploit SZPOS0; et. i.
        pose proof (Int64.eq_spec i2 Int64.zero).
        destruct (Int64.eq i2 Int64.zero) eqn: ?.
        { subst. exfalso. 
          unfold weak_valid, Ptrofs.sub, Ptrofs.of_int64 in *.
          change (Ptrofs.unsigned (Ptrofs.repr (Int64.unsigned _))) with 0 in *.
          change (0 - Ptrofs.unsigned a) with (- Ptrofs.unsigned a) in *.
          eapply weak_valid_nil_paddr_base; et. nia. }
        unfold cmp_ptr_join. ss.
        iCombine "CONC CONC_PRE" as "CONC".
        iOwnWf "CONC" as wfconc.
        ur in wfconc. specialize (wfconc (Some b0)). ss. destruct dec; clarify.
        hexploit (SIM_CONC (Some b0)). i. 
        apply OneShot.oneshot_initialized in wfconc. 
        des; rewrite wfconc in *; inv H14; clarify.
        hexploit paddr_no_overflow_cond_lt; et. i.
        assert (to_ptr_val mem_tgt (Vlong i2) = Vptr b0 (Ptrofs.repr (Int64.unsigned i2 - Ptrofs.unsigned base))).
        { unfold to_ptr_val, Mem.to_ptr.
          des_ifs; [apply Maps.PTree.gselectf in Heq1|apply Maps.PTree.gselectnf in Heq1]; des.
          - ss. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in *.
            des_ifs; bsimpl; des; clarify.
            hexploit (PERMinrange0 (Int64.unsigned i2 - Ptrofs.unsigned base)).
            { unfold size_chunk in *. des_ifs. destruct tag0; (hexploit COMMON0 + hexploit DYNAMIC0); et; nia. }
            i. des. 
            pose proof (mem_tgt.(Mem.no_concrete_overlap) (Int64.unsigned i2)).
            red in H19. hexploit (H19 b0 b1).
            { econs; et.
              - epose proof (mem_tgt.(Mem.access_max) b0 _).
                rewrite H16 in H20. unfold Mem.perm_order'' in *. des_ifs. et.
              - destruct base; destruct i2; ss.
                change Int64.modulus with (Ptrofs.max_unsigned + 1) in *.
                change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
            { econs; et. destruct i2; ss. nia. }
            i. subst. rewrite Heq3 in *. clarify.
          - exfalso. apply Heq1. esplits; et. unfold Mem.denormalize_aux.
            rewrite <- H17. unfold size_chunk in *. des_ifs. bsimpl.
            hexploit (PERMinrange0 (Int64.unsigned i2 - Ptrofs.unsigned base)); try solve [destruct tag0; (hexploit COMMON0 + hexploit DYNAMIC0); et; nia].
            i. unfold Mem.is_valid, Mem.addr_is_in_block in *. rewrite <- H17 in Heq2. des.
            { hexploit (mem_tgt.(Mem.nextblock_noaccess) b0); try solve [rewrite H13; et].
              apply Pos.ltb_ge in Heq2. unfold Coqlib.Plt. nia. rewrite H16. et. }
            { des_ifs; bsimpl; des.
              { rewrite PERMoutrange0 in H16; clarify. destruct tag0; (hexploit COMMON0 + hexploit DYNAMIC0); et; nia. }
              { destruct i2; destruct base; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
              { hexploit (mem_tgt.(Mem.access_max)). rewrite Heq4. rewrite H16. i. inv H19. } } }
        rewrite H15. unfold to_ptr_val at 1. unfold to_int_val at 2. ss.
        unfold cmp_ptr. des_ifs_safe. unfold Val.cmplu_bool at 2.
        rewrite Ptrofs.unsigned_repr; [|destruct base; ss; nia].
        assert (Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1) = true).
        { bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          unfold size_chunk in *. des_ifs. destruct i1; ss.
          hexploit (PERMinrange intval).
          { destruct tag; try solve [hexploit COMMON; et; nia| hexploit DYNAMIC; et; des; nia]. }
          i. des. unfold Mem.perm, Mem.perm_order' in *.
          rewrite H16 in *. apply n. econs. }
        assert (Mem.valid_pointer mem_tgt b0 (Int64.unsigned i2 - Ptrofs.unsigned base) = true).
        { clear H16. bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          unfold size_chunk in *. des_ifs. destruct i2; destruct base; ss.
          hexploit (PERMinrange0 (intval - intval0)).
          { destruct tag0; try solve [hexploit COMMON0; et; nia| hexploit DYNAMIC0; et; des; nia]. }
          i. des. unfold Mem.perm, Mem.perm_order' in *.
          rewrite H16 in *. apply n. econs. }
        rewrite H18. rewrite H16. ss. destruct eq_block; clarify.
        Local Opaque Val.cmplu_bool.
        des_ifs; hred_r; des_ifs; hred_r.
        Local Transparent Val.cmplu_bool.
        * iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iSplit; ss. iExists _. iFrame. ss.
        * iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iDestruct "CONC" as "[CONC ?]".
          iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplit; ss. iSplit; ss. iExists _. iFrame. ss.
        * unfold Val.cmplu_bool, to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
          des_ifs. ss. clarify. hexploit Int64.eq_spec. rewrite Heq5.
          i. subst. unfold Mem.valid_pointer in *.
          do 2 destruct Mem.perm_dec; ss; clarify.
          unfold Mem.perm, Mem.perm_order' in *. des_ifs.
          hexploit (mem_tgt.(Mem.weak_valid_address_range) b); et.
          { apply Ptrofs.unsigned_range. }
          { unfold Mem._weak_valid_pointer, Mem._valid_pointer.
            pose proof (mem_tgt.(Mem.access_max) b (Ptrofs.unsigned i1)).
            rewrite Heq3 in H19. unfold Mem.perm_order'' in *.
            des_ifs. rewrite Heq7. left. econs. }
          i. inv H19; ss.
          rewrite Int64.unsigned_repr in *.
          2,3,4: change Int64.max_unsigned with (Ptrofs.modulus - 1); nia.
          pose proof (mem_tgt.(Mem.no_concrete_overlap) (z0 + Ptrofs.unsigned i1)).
          red in H19. hexploit (H19 b0 b).
          { econs; et.
            - pose proof (mem_tgt.(Mem.access_max) b0 (z0 + Ptrofs.unsigned i1 - Ptrofs.unsigned base)).
              rewrite Heq1 in H20. unfold Mem.perm_order'' in *. des_ifs. et.
            - destruct base; destruct i1; ss.
              change Int64.modulus with (Ptrofs.max_unsigned + 1) in *.
              change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia. }
          { econs; et.
            - pose proof (mem_tgt.(Mem.access_max) b (Ptrofs.unsigned i1)).
              rewrite Heq3 in H20. unfold Mem.perm_order'' in *. des_ifs.
              replace (_ + _ - _) with (Ptrofs.unsigned i1) by nia. et.
            - destruct i1; ss. nia. }
          i. clarify.
      + iDestruct "P" as "%". des. clarify.
        iDestruct "A" as "%". des. clarify.
        unfold cmp_ptr. des_ifs_safe. unfold Val.cmplu_bool.
        unfold "#^" in *. destruct eq_block. { clarify. rewrite <- Heqo in *. clarify. }
        hred_r.
        iCombine "ALLOC ALLOC_PRE" as "ALLOC". 
        iCombine "SZ SZ_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc.
        iOwnWf "SZ" as wfsz.
        iDestruct "ALLOC" as "[ALLOC ALLOC_PRE]".
        iDestruct "SZ" as "[SZ SZ_PRE]".
        iCombine "ALLOC ALLOC0_PRE" as "ALLOC". 
        iCombine "SZ SZ0_PRE" as "SZ".
        iOwnWf "ALLOC" as wfalloc0.
        iOwnWf "SZ" as wfsz0.
        iDestruct "ALLOC" as "[ALLOC ALLOC0_PRE]".
        iDestruct "SZ" as "[SZ SZ0_PRE]".
        ur in wfalloc. ur in wfsz. rewrite URA.unit_idl in wfalloc. des.
        apply pw_extends in wfalloc. red in wfalloc.
        ur in wfalloc0. ur in wfsz0. rewrite URA.unit_idl in wfalloc0. des.
        apply pw_extends in wfalloc0. red in wfalloc0. ur in wfalloc1.
        specialize (wfsz (Some b)).
        specialize (wfsz0 (Some b0)).
        specialize (wfalloc b).
        specialize (wfalloc0 b0).
        hexploit (SIM_ALLOC (Some b)).
        hexploit (SIM_ALLOC (Some b0)).
        i. des. unfold __allocated_with in *. destruct dec; clarify.
        destruct dec; clarify.
        apply Consent.extends in wfalloc; et. red in wfalloc. des. rewrite wfalloc3 in *.
        apply Consent.extends in wfalloc0; et. red in wfalloc0. des. rewrite wfalloc4 in *.
        apply OneShot.oneshot_initialized in wfsz.
        apply OneShot.oneshot_initialized in wfsz0.
        destruct wfsz as [wfsz|wfsz]; rewrite wfsz in H8; inv H8; clarify.
        destruct wfsz0 as [wfsz0|wfsz0]; rewrite wfsz0 in H4; inv H4; clarify.
        destruct m, m0. unfold "#^", valid in *. ss. rewrite Heqo in *. rewrite Heqo0 in *.
        hexploit SZPOS; et. i.
        hexploit SZPOS0; et. i.
        assert (Mem.valid_pointer mem_tgt b0 (Ptrofs.unsigned i2) = true).
        { bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          unfold size_chunk in *. des_ifs. destruct i2; ss.
          hexploit (PERMinrange0 intval).
          { destruct tag0; try solve [hexploit COMMON0; et; nia| hexploit DYNAMIC0; et; des; nia]. }
          i. des. unfold Mem.perm, Mem.perm_order' in *.
          rewrite H11 in *. apply n0. econs. }
        assert (Mem.valid_pointer mem_tgt b (Ptrofs.unsigned i1) = true).
        { bsimpl. unfold Mem.valid_pointer.
          repeat destruct Mem.perm_dec; ss; clarify; et; exfalso.
          unfold size_chunk in *. des_ifs. destruct i1; ss.
          hexploit (PERMinrange intval).
          { destruct tag; try solve [hexploit COMMON; et; nia| hexploit DYNAMIC; et; des; nia]. }
          i. des. unfold Mem.perm, Mem.perm_order' in *.
          rewrite H12 in *. apply n0. econs. }
        rewrite H11. rewrite H12. des_ifs. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT ALLOC CONC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. iSplit; ss.
    - unfold cmp_ptr_hoare7. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[[[% P] A] %]".
      do 2 unfold has_offset, _has_offset.
      destruct blk; clarify.
      iDestruct "P" as "[ALLOC_PRE [SZ_PRE P]]".
      destruct blk; clarify.
      iDestruct "A" as "[ALLOC0_PRE [SZ0_PRE A]]".
      des; clarify. hred_r.
      iApply isim_pget_tgt. hred_r.
      destruct v0; clarify; des_ifs_safe;
      destruct v; clarify; des_ifs_safe.
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        iDestruct "A" as (a0) "[CONC0_PRE %]". des. clarify.
        unfold cmp_ptr. unfold Val.cmplu_bool. des_ifs_safe. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. iSplitL "CONC_PRE".
        { iSplit; ss. 2:{ iExists _. iFrame. ss. }
          iPureIntro. f_equal. admit "". }
        { iExists _. iFrame. ss. }
      + iDestruct "P" as "%". des. clarify.
        iDestruct "A" as (a) "[CONC_PRE %]". des. clarify.
        admit "no_overflow lemma needed".
      + iDestruct "P" as (a) "[CONC_PRE %]". des. clarify.
        iDestruct "A" as "%". des. clarify.
        admit "no_overflow lemma needed".
      + iDestruct "P" as "%". des. clarify.
        iDestruct "A" as "%". des. clarify.
        unfold cmp_ptr. des_ifs_safe. unfold Val.cmplu_bool.
        admit "no_overlap lemma needed".
    Unshelve. all: et.
  Qed.

  Lemma sim_non_null :
    sim_fnsem wf top2
      ("non_null?", fun_to_tgt "Mem" (to_stb []) (mk_pure non_null_spec))
      ("non_null?", cfunU non_nullF).
  Proof.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. iIntros "[INV PRE]". des_ifs. ss.
    do 2 unfold has_offset, _has_offset, points_to, _points_to.
    iDestruct "PRE" as "[[% P] %]". des.
    destruct blk; clarify.
    iDestruct "P" as "[ALLOC_PRE [SZ_PRE A]]".
    des; clarify. unfold inv_with.
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify.
    unfold non_nullF. hred_r.
    iApply isim_pget_tgt. hred_r.
    assert (IntPtrRel.to_ptr_val mem_tgt v = Vptr b i).
    { admit "". }
    rewrite H4.
    assert (Mem.weak_valid_pointer mem_tgt b (Ptrofs.unsigned i) = true).
    { admit "". }
    rewrite H6. hred_r.
    iApply isim_apc. iExists None.
    hred_l. iApply isim_choose_src. iExists _.
    iApply isim_ret. iSplitL "CNT CONC ALLOC SZ".
    { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
    iSplit; ss. iFrame. ss.
  Unshelve. et.
  Qed.

  Lemma sim_malloc :
    sim_fnsem wf top2
      ("malloc", fun_to_tgt "Mem" (to_stb []) (mk_pure malloc_spec))
      ("malloc", cfunU mallocF).
  Proof.
  Admitted.

  Lemma sim_mfree :
    sim_fnsem wf top2
      ("free", fun_to_tgt "Mem" (to_stb []) (mk_pure mfree_spec))
      ("free", cfunU mfreeF).
  Proof.
  Admitted.

  Lemma sim_memcpy :
    sim_fnsem wf top2
      ("memcpy", fun_to_tgt "Mem" (to_stb []) (mk_pure memcpy_spec))
      ("memcpy", cfunU memcpyF).
  Proof.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. unfold "@".
    iIntros "[INV PRE]".
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify. unfold memcpyF. do 2 (try destruct x as [?|x]).
    - unfold memcpy_hoare0. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[PRE %]".
      iDestruct "PRE" as (al sz mvs_src) "[[[[% F] D] P] A]".
      do 2 unfold has_offset, points_to, _has_offset, _points_to.
      destruct blk; clarify.
      destruct blk; clarify.
      iDestruct "P" as "[SZ_PRE P]".
      iDestruct "P" as (ofs) "[[[CNT_PRE [SZ0_PRE P]] %] LEN]".
      iDestruct "A" as "[SZ1_PRE A]".
      iDestruct "A" as (ofs0) "[[[CNT0_PRE [SZ2_PRE A]] %] LEN0]".
      iDestruct "D" as "[ALLOC_PRE [SZ3_PRE D]]".
      iDestruct "F" as "[ALLOC0_PRE [SZ4_PRE F]]".
      do 7 (destruct H5 as [? H5]). clarify. hred_r.
      iApply isim_upd.
      assert (Mem.loadbytes mem_tgt b (Ptrofs.unsigned ofs) sz = Some mvs_src).
      { admit "". }
      assert (Mem.range_perm mem_tgt b0 (Ptrofs.unsigned ofs0) (Ptrofs.unsigned ofs0 + length mvs_src) Cur Writable).
      { admit "". }
      iCombine "CNT CNT0_PRE" as "CNT".
      iPoseProof (OwnM_Upd with "CNT") as ">[CNT CNT0_POST]".
      + admit "".
      + iModIntro.
        destruct dec.
        { hred_r. subst. destruct l; clarify. destruct mvs_src; clarify.
          iApply isim_apc. iExists None.
          hred_l. iApply isim_choose_src. iExists _.
          iApply isim_ret. admit "".
          (* iSplitL "CNT CONC ALLOC SZ".
          { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
          iSplit; ss. iFrame. iSplitR "LEN0 A". 2:{ iExists _. iFrame. iSplit; ss. admit "unit". }
          iSplit; ss. iExists _. iFrame. ss.  *)
          }
        hred_r. iApply isim_pget_tgt. hred_r.
        assert (i0 = ofs) by admit "".
        assert (i = ofs0) by admit "".
        subst.
        assert (Mem.to_ptr v mem_tgt = Some (Vptr b0 ofs0)) by admit "".
        assert (Mem.to_ptr v0 mem_tgt = Some (Vptr b ofs)) by admit "".
        rewrite H15. rewrite H16. hred_r.
        set (_ && _) as chk1.
        assert (chk1 = true).
        { unfold chk1. bsimpl.
          repeat destruct dec; repeat destruct Zdivide_dec; destruct Coqlib.zle; ss; clarify; et; try tauto. }
        rewrite H17. ss. destruct Coqlib.zle; clarify.
        destruct Zdivide_dec; clarify. ss.
        set (_ || _) as chk4.
        assert (chk4 = true).
        { admit "". }
        rewrite H18. ss.
        rewrite H7. hred_r.
        Local Transparent Mem.storebytes.
        unfold Mem.storebytes.
        destruct Mem.range_perm_dec; clarify. hred_r.
        iApply isim_pput_tgt. hred_r.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret. iModIntro. admit "".
    - unfold memcpy_hoare1. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "[PRE %]".
      iDestruct "PRE" as (al sz) "[[% P] A]".
      do 2 unfold has_offset, points_to, _has_offset, _points_to.
      destruct blk; clarify.
      iDestruct "A" as "[SZ_PRE A]".
      iDestruct "A" as (ofs) "[[[CNT_PRE [SZ0_PRE A]] %] LEN]".
      iDestruct "P" as "[ALLOC_PRE [SZ3_PRE P]]".
      do 5 (destruct H5 as [? H5]). clarify. hred_r.
      assert (Mem.loadbytes mem_tgt b (Ptrofs.unsigned ofs) sz = Some l).
      { admit "". }
      assert (Mem.range_perm mem_tgt b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + length l) Cur Writable).
      { admit "". }
      destruct dec.
      { hred_r. subst. destruct l; clarify.
        iApply isim_apc. iExists None.
        hred_l. iApply isim_choose_src. iExists _.
        iApply isim_ret.
        iSplitL "CNT CONC ALLOC SZ".
        { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
        iSplit; ss. iFrame. iSplitR "LEN A". 2:{ iExists _. iFrame. iSplit; ss. admit "unit". }
        ss. }
      hred_r. iApply isim_pget_tgt. hred_r.
      assert (i = ofs) by admit "".
      subst.
      assert (Mem.to_ptr v mem_tgt = Some (Vptr b ofs)) by admit "".
      rewrite H12. hred_r.
      set (_ && _) as chk1.
      assert (chk1 = true).
      { unfold chk1. bsimpl.
        repeat destruct dec; repeat destruct Zdivide_dec; destruct Coqlib.zle; ss; clarify; et; try tauto. }
      rewrite H13. ss. destruct Coqlib.zle; clarify.
      destruct Zdivide_dec; clarify. ss.
      set (_ || _) as chk4.
      assert (chk4 = true).
      { admit "". }
      rewrite H14. ss.
      rewrite H6. hred_r.
      Local Transparent Mem.storebytes.
      unfold Mem.storebytes.
      destruct Mem.range_perm_dec; clarify. hred_r.
      iApply isim_pput_tgt. hred_r.
      iApply isim_apc. iExists None.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. admit "".
    Unshelve. all: et. { admit "". } { admit "". }
  Qed.

  Lemma sim_capture :
    sim_fnsem wf top2
      ("capture", fun_to_tgt "Mem" (to_stb []) (mk_pure capture_spec))
      ("capture", cfunU captureF).
  Proof.
    econs; ss. red; ss. apply isim_fun_to_tgt; ss.
    i. unfold "@".
    iIntros "[INV PRE]".
    iDestruct "INV" as (tt) "[INV %]".
    iDestruct "INV" as (mem_tgt memcnt_src memalloc_src memsz_src memconc_src) "[[[[% CNT] ALLOC] CONC] SZ]".
    des; clarify. unfold captureF. do 2 (try destruct x as [?|x]).
    { unfold capture_hoare0. des_ifs_safe. ss. clarify.
      iDestruct "PRE" as "%". des. clarify. hred_r.
      iApply isim_pget_tgt. hred_r.
      change Mem.mem' with Mem.mem in *. hred_r.
      destruct Vnullptr eqn:?; clarify.
      rewrite <- Heqv. hred_r.
      iApply isim_apc. iExists None.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplit; ss. 
      iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
    unfold capture_hoare1. des_ifs_safe. ss. clarify.
    iDestruct "PRE" as "[[% P] %]". des. clarify. hred_r.
    unfold has_offset, _has_offset.
    destruct blk; clarify.
    iDestruct "P" as "[ALLOC_PRE [SZ_PRE P]]".
    iApply isim_pget_tgt. hred_r.
    change Mem.mem' with Mem.mem in *. hred_r.
    Local Transparent equiv_prov.
    destruct v; clarify; hred_r; ss.
    { iApply isim_apc. iExists None.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplitL "ALLOC CONC SZ CNT".
      { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
      iSplit; ss. iFrame. iExists _.
      unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et.
      iSplit; ss. admit "". }
    iDestruct "P" as "%". des. clarify.
    unfold Coqlib.Plt.
    destruct Coqlib.plt; ss. 2:{ admit "impossible". }
    hred_r. iApply isim_choose_tgt.
    iIntros (x). destruct x. destruct x. ss. hred_r.
    iApply isim_pput_tgt. hred_r.
    iApply isim_apc. iExists None.
    hred_l. iApply isim_choose_src. iExists _.
    iApply isim_upd.

    iPoseProof (OwnM_Upd with "CONC") as ">[CONC CONC_POST]".
    { admit "". }
    iModIntro.
    iApply isim_ret. iModIntro. admit "".
    (* iSplitL "ALLOC CONC SZ CNT".
    { iExists _. iSplit; ss. iExists _,_,_,_,_. iFrame. iPureIntro. et. }
    iSplit; ss. iFrame. iExists _.
    unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et.
    iSplit; ss. admit "". *)
  Unshelve. all: et.
  Qed.

  Theorem correct_mod: ModPair.sim ClightDmMem1.Mem ClightDmMem0.Mem.
  Proof.
    econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); ss; cycle 1.
    { exists tt. des_ifs.
      - apply init_wf; et.
      - rewrite <- wf_iff in Heq0. clarify.
      - rewrite wf_iff in Heq. clarify.
      - admit "". }
    repeat (match goal with |- Forall2 _ _ _ => econs end).
    - apply sim_salloc.
    - apply sim_sfree.
    - apply sim_load.
    - apply sim_store.
    - apply sim_sub_ptr.
    - apply sim_cmp_ptr.
    - apply sim_non_null.
    - apply sim_malloc.
    - apply sim_mfree.
    - apply sim_memcpy.
    - apply sim_capture.
  Qed.


  (* Theorem correct_modsem: forall sk, ModSemPair.sim (SModSem.to_tgt (to_stb []) *)
(*                                            (Mem1.SMemSem (negb ∘ csl) sk)) (Mem0.MemSem csl sk). *)
(*   Proof. *)
(*    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3. *)
(*    { ss. } *)
(*     { ss. eexists. econs; ss. eapply to_semantic. *)
(*       iIntros "H". iSplits; ss; et. *)
(*       { iPureIntro. ii. unfold Mem.load_mem, initial_mem_mr. *)
(*         cbn. uo. des_ifs; et; try (by econs; et). } *)
(*       { iPureIntro. ii. ss. uo. des_ifs. *)
(*         apply nth_error_Some. ii. clarify. } *)
(*     } *)





(*     econs; ss. *)
(*     { unfold allocF. init. *)
(*       harg. fold wf. steps. hide_k. rename x into sz. *)
(*       { mDesAll; ss. des; subst. *)
(*         des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify. *)
(*         steps. unhide_k. steps. des_ifs; clarify. *)
(*         2:{ bsimpl; des; ss; apply sumbool_to_bool_false in Heq; try lia. } *)
(*         steps. astart 0. astop. *)
(*         renamer. *)
(*         set (blk := mem_tgt0.(Mem.nb) + x). *)

(*         mAssert _ with "INV" as "INV". *)
(*         { iApply (OwnM_Upd with "INV"). *)
(*           eapply Auth.auth_alloc2. *)
(*           instantiate (1:=(_points_to (blk, 0%Z) (repeat (Vundef) sz))). *)
(*           mOwnWf "INV". *)
(*           clear - WF0 WFTGT SIM. *)
(*           ss. do 2 ur. ii. rewrite unfold_points_to. des_ifs. *)
(*           - bsimpl. des. des_sumbool. subst. hexploit (SIM blk k0); et. intro T. *)
(*             inv T; eq_closure_tac. *)
(*             + exploit WFTGT; et. i; des. lia. *)
(*             + rewrite URA.unit_idl. Ztac. rewrite repeat_length in *. rewrite Z.sub_0_r. rewrite repeat_nth_some; [|lia]. ur. ss. *)
(*           - rewrite URA.unit_id. do 2 eapply lookup_wf. eapply Auth.black_wf; et. *)
(*         } *)
(*         mUpd "INV". mDesOwn "INV". steps. *)

(*         force_l. eexists. steps. hret _; ss. iModIntro. iSplitR "A"; cycle 1. *)
(*         { iSplitL; ss. iExists _. iSplitR; ss. } *)
(*         iExists _, _. iSplitR; ss. iPureIntro. esplits; et. *)
(*         - i. destruct (mem_tgt0.(Mem.cnts) blk ofs) eqn:T. *)
(*           { exfalso. exploit WFTGT; et. i; des. lia. } *)
(*           ss. do 2 ur. *)
(*           exploit SIM; et. rewrite T. intro U. inv U. rewrite unfold_points_to. ss. rewrite repeat_length. *)
(*           destruct (dec b blk); subst; ss. *)
(*           * unfold update. des_ifs_safe. rewrite <- H1. rewrite URA.unit_idl. *)
(*             rewrite Z.sub_0_r. rewrite Z.add_0_l. des_ifs. *)
(*             { bsimpl. des. Ztac. rewrite repeat_nth_some; try lia. econs. } *)
(*           * rewrite URA.unit_id. unfold update. des_ifs. *)
(*         - clear - WFTGT. ii. ss. unfold update in *. des_ifs. exploit WFTGT; et. i; des. r. lia. *)
(*       } *)
(*     } *)





(*     econs; ss. *)
(*     { unfold freeF. init. *)
(*       harg. fold wf. steps. hide_k. *)
(*       { des_ifs_safe (mDesAll; ss). des; subst. *)
(*         des_ifs; mDesAll; ss. des; subst. clarify. rewrite Any.upcast_downcast in *. clarify. *)
(*         steps. unhide_k. steps. astart 0. astop. *)
(*         renamer. rename n into b. rename z into ofs. *)
(*         rename a into v. rename WF into SIMWF. *)
(*         mCombine "INV" "A". mOwnWf "INV". *)
(*         assert(HIT: memk_src0 b ofs = (Some v)). *)
(*         { clear - WF. *)
(*           dup WF. eapply Auth.auth_included in WF. des. eapply pw_extends in WF. eapply pw_extends in WF. *)
(*           spc WF. rewrite _points_to_hit in WF. *)
(*           eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et. *)
(*         } *)
(*         set (memk_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs *)
(*                                          then (ε: URA.car (t:=Excl.t _)) else memk_src0 _b _ofs). *)
(*         assert(WF': URA.wf (memk_src1: URA.car (t:=Mem1._memRA))). *)
(*         { clear - WF. unfold memk_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des. *)
(*           des_ifs; et. *)
(*           - rp; [eapply URA.wf_unit|ss]. *)
(*           - do 2 eapply lookup_wf; et. *)
(*         } *)
(*         hexploit (SIM b ofs); et. rewrite HIT. intro B. inv B. *)
(*         force_r. *)
(*         { unfold Mem.free in *. des_ifs. } *)
(*         rename t into mem_tgt1. *)

(*         mAssert _ with "INV" as "INV". *)
(*         { iApply (OwnM_Upd with "INV"). *)
(*           Local Transparent points_to. *)
(*           eapply Auth.auth_dealloc. *)
(*           instantiate (1:=memk_src1). *)
(*           clear - WF'. *)

(*           r. i. rewrite URA.unit_idl. *)
(*           Local Opaque Mem1._memRA. *)
(*           ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify. *)
(*           esplits; et. *)
(*           Local Transparent Mem1._memRA. *)
(*           unfold memk_src1. ss. *)
(*           apply func_ext. intro _b. apply func_ext. intro _ofs. *)
(*           des_ifs. *)
(*           - bsimpl; des; des_sumbool; subst. *)
(*             subst memk_src1. do 2 ur in WF'. do 2 spc WF'. des_ifs; bsimpl; des; des_sumbool; ss. *)
(*             clear - H0. *)
(*             do 2 ur in H0. *)
(*             specialize (H0 b ofs). rewrite _points_to_hit in H0. eapply Excl.wf in H0. des; ss. *)
(*           - rewrite unfold_points_to in *. do 2 ur. do 2 ur in H0. *)
(*             bsimpl. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia; try rewrite URA.unit_idl; try refl. *)
(*         } *)
(*         mUpd "INV". *)
(*         steps. force_l. eexists. steps. hret _; ss. iModIntro. iSplitL; cycle 1. *)
(*         { iPureIntro. ss. } *)
(*         iExists _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et. *)
(*         - { i. unfold Mem.free in _UNWRAPU. des_ifs. ss. *)
(*             subst memk_src1. ss. *)
(*             destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify. *)
(*             - unfold update. des_ifs. *)
(*             - des_ifs. *)
(*               { Psimpl. bsimpl; des; des_sumbool; ss; clarify. } *)
(*               replace (update (Mem.cnts mem_tgt0) b (update (Mem.cnts mem_tgt0 b) ofs None) b0 ofs0) with *)
(*                   (Mem.cnts mem_tgt0 b0 ofs0); cycle 1. *)
(*               { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. } *)
(*               et. *)
(*           } *)
(*         - clear - _UNWRAPU WFTGT. ii. unfold Mem.free in *. des_ifs. ss. *)
(*           unfold update in *. des_ifs; eapply WFTGT; et. *)
(*       } *)
(*     } *)





(*     econs; ss. *)
(*     { unfold loadF. init. *)
(*       harg. fold wf. steps. hide_k. *)
(*       { des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify. *)
(*         steps. unhide_k. steps. astart 0. astop. *)
(*         renamer. rename n into b. rename z into ofs. *)
(*         rename WF into SIMWF. *)
(*         mCombine "INV" "A". mOwnWf "INV". *)
(*         assert(T: memk_src0 b ofs = (Some v)). *)
(*         { clear - WF. *)
(*           dup WF. *)
(*           eapply Auth.auth_included in WF. des. *)
(*           eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF. des; ss. *)
(*           eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et. *)
(*         } *)
(*         hexploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load. *)
(*         mDesOwn "INV". *)
(*         force_r; ss. clarify. steps. force_l. esplits. steps. *)
(*         hret _; ss. iModIntro. iFrame. iSplitL; et. *)
(*       } *)
(*     } *)





(*     econs; ss. *)
(*     { unfold storeF. init. *)
(*       harg. fold wf. steps. hide_k. *)
(*       { des_ifs_safe (mDesAll; ss). des; subst. clarify. rewrite Any.upcast_downcast in *. clarify. *)
(*         steps. unhide_k. steps. astart 0. astop. *)
(*         renamer. *)
(*         rename n into b. rename z into ofs. rename v into v1. *)
(*         rename a into v0. rename WF into SIMWF. *)
(*         steps. *)
(*         mCombine "INV" "A". mOwnWf "INV". *)
(*         assert(T: memk_src0 b ofs = (Some v0)). *)
(*         { clear - WF. *)
(*           dup WF. *)
(*           eapply Auth.auth_included in WF. des. *)
(*           eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF. *)
(*           des; ss. *)
(*           eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et. *)
(*         } *)
(*         hexploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.store. des_ifs. steps. *)
(*         set (memk_src1 := fun _b _ofs => if dec _b b && dec _ofs ofs then (Some v1: URA.car (t:=Excl.t _)) else memk_src0 _b _ofs). *)
(*         assert(WF': URA.wf (memk_src1: URA.car (t:=Mem1._memRA))). *)
(*         { clear - WF. unfold memk_src1. do 2 ur. ii. eapply URA.wf_mon in WF. ur in WF. des. *)
(*           des_ifs; et. *)
(*           - bsimpl; des; des_sumbool; subst. ur; ss. *)
(*           - do 2 eapply lookup_wf; et. *)
(*         } *)
(*         mAssert _ with "INV" as "INV". *)
(*         { iApply (OwnM_Upd with "INV"). *)
(*           eapply Auth.auth_update with (a':=memk_src1) (b':=_points_to (b, ofs) [v1]); et. *)
(*           clear - wf WF'. ii. des. subst. esplits; et. *)
(*           do 2 ur in WF'. do 2 spc WF'. *)
(*           subst memk_src1. ss. des_ifs; bsimpl; des; des_sumbool; ss. *)
(*           do 2 ur. do 2 (apply func_ext; i). des_ifs. *)
(*           - bsimpl; des; des_sumbool; subst. rewrite _points_to_hit. *)
(*             do 2 ur in WF. do 2 spc WF. rewrite _points_to_hit in WF. eapply Excl.wf in WF. rewrite WF. ur; ss. *)
(*           - bsimpl; des; des_sumbool; rewrite ! _points_to_miss; et. *)
(*         } *)
(*         mUpd "INV". mDesOwn "INV". *)

(*         mEval ltac:(fold (points_to (b,ofs) [v1])) in "A". *)
(*         force_l. eexists. steps. *)
(*         hret _; ss. iModIntro. iFrame. iSplitL; ss; et. *)
(*         iExists _, _. iSplitR "INV"; et. iPureIntro. esplits; ss; et. *)
(*         - ii. cbn. des_ifs. *)
(*           + bsimpl; des; des_sumbool; subst. do 2 spc SIM. rewrite T in *. inv SIM. *)
(*             unfold memk_src1. rewrite ! dec_true; ss. econs. *)
(*           + replace (memk_src1 b0 ofs0) with (memk_src0 b0 ofs0); et. *)
(*             unfold memk_src1. des_ifs; bsimpl; des; des_sumbool; clarify; ss. *)
(*         - ii. ss. des_ifs. *)
(*           + bsimpl; des; des_sumbool; subst. eapply WFTGT; et. *)
(*           + eapply WFTGT; et. *)
(*       } *)
(*     } *)





(*     econs; ss. *)
(*     { unfold cmpF. init. *)
(*       harg. fold wf. steps. hide_k. *)
(*       { des_ifs_safe (mDesAll; ss). des; subst. clarify. *)
(*         steps. unhide_k. steps. astart 0. astop. *)
(*         renamer. *)
(*         rename b into result. rename c into resource. rename WF into SIMWF. *)
(*         assert (VALIDPTR: forall b ofs v (WF: URA.wf ((Auth.black (memk_src0: URA.car (t:=Mem1._memRA))) ⋅ ((b, ofs) |-> [v]))), *)
(*                    Mem.valid_ptr mem_tgt0 b ofs = true). *)
(*         { clear - SIM. i. cut (memk_src0 b ofs = Some v). *)
(*           - i. unfold Mem.valid_ptr. *)
(*             specialize (SIM b ofs). rewrite H in *. inv SIM. ss. *)
(*           - clear - WF. *)
(*             dup WF. *)
(*             eapply Auth.auth_included in WF. des. *)
(*             eapply pw_extends in WF. eapply pw_extends in WF. spc WF. rewrite _points_to_hit in WF. *)
(*             des; ss. *)
(*             eapply Excl.extends in WF; ss. do 2 eapply lookup_wf. eapply Auth.black_wf. eapply URA.wf_mon; et. *)
(*         } *)
(*         steps. *)
(*         mCombine "INV" "A". mOwnWf "INV". Fail mDesOwn "INV". (*** TODO: BUG!! FIXME ***) *)

(*         mDesOr "PRE". *)
(*         { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps. *)
(*           erewrite VALIDPTR; et. ss. steps. *)
(*           force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et. *)
(*         } *)
(*         mDesOr "PRE". *)
(*         { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps. *)
(*           erewrite VALIDPTR; et. ss. steps. *)
(*           force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et. *)
(*         } *)
(*         mDesOr "PRE". *)
(*         { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps. *)
(*           erewrite VALIDPTR; et; cycle 1. *)
(*           { rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. } *)
(*           erewrite VALIDPTR; et; cycle 1. *)
(*           { erewrite URA.add_comm with (a:=(a, a0) |-> [a1]) in WF. *)
(*             rewrite URA.add_assoc in WF. eapply URA.wf_mon in WF; et. } *)
(*           rewrite URA.add_comm in WF. eapply URA.wf_mon in WF. ur in WF; ss. steps. *)
(*           replace (dec a a2 && dec a0 a3 ) with false; cycle 1. *)
(*           { clear - WF. *)
(*             exploit _points_to_disj; et. intro NEQ. des; try (by rewrite dec_false; ss). *)
(*             erewrite dec_false with (x0:=a0); ss. rewrite andb_false_r; ss. *)
(*           } *)
(*           steps. force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et. *)
(*         } *)
(*         mDesOr "PRE". *)
(*         { mDesAll; subst. rewrite Any.upcast_downcast in *. clarify. steps. *)
(*           erewrite VALIDPTR; et. ss. steps. rewrite ! dec_true; ss. steps. *)
(*           force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et. *)
(*         } *)
(*         { mDesAll; subst. des; subst. rewrite Any.upcast_downcast in *. clarify. steps. *)
(*           force_l. eexists. steps. hret _; ss. iModIntro. iDestruct "INV" as "[INV A]". iSplitR "A"; ss; et. *)
(*         } *)
(*       } *)
(*     } *)
(*   Unshelve. *)
(*     all: ss. all: try exact 0. *)
(*   Qed. *)

End SIMMODSEM.
