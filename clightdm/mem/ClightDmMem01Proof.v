Require Import CoqlibCCR Any.
Require Import Skeleton.
Require Import ModSem Behavior SimModSem.
Require Import PCM.
Require Import HoareDef STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightDmMem0 ClightDmMem1 ClightDmMemAux.
From compcert Require Import Ctypes Floats Integers Values Memory AST Clight Clightdefs.


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
      (Qread: (q < Q1)%Qp -> perm Cur = Some p /\ perm_order p Readable)
      (Qwrite: q = Q1 -> perm Cur = Some p /\ perm_order p Writable)
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
      set {| blk := Some (mem_tgt.(Mem.nextblock)); sz := sz; SZPOS := H5 |} as m.
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
      { rewrite Mem.nextblock_noaccess in Qread; unfold Coqlib.Plt; try nia.
        rewrite Mem.nextblock_noaccess in Qwrite; unfold Coqlib.Plt; try nia.
        rewrite Qp_le_lteq in Qwf. des; try spc Qwrite; try spc Qread; des; clarify. }
      do 2 ur. rewrite <- H7. rewrite URA.unit_idl. rewrite Maps.ZMap.gi.
      case_points_to; ss; cycle 1.
      { rewrite repeat_length in *. destruct Coqlib.zlt; ss. nia. }
      destruct nth_error eqn: ?; cycle 1.
      { rewrite nth_error_None in Heqo. nia. }
      rewrite repeat_length in *. destruct Coqlib.zlt; ss; try nia.
      rewrite repeat_nth in *. des_ifs.
      econs; ss. i. split; ss. econs.
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
    (* { unfold loadF. init.
      harg. fold wf. steps. hide_k.
      { mDesAll; ss. des; subst.
        mRename "A5" into "CNT". mRename "A4" into "ALLOCATED". mRename "A3" into "CONC". mRename "A2" into "SZ".
        mRename "A1" into "OFS". mRename "A" into "PTRTO".
        rewrite Any.upcast_downcast in *.
        steps. unhide_k. steps. astart (Ord.from_nat 0%nat). astop.
        steps. force_l. eexists.
        mAssertPure (Mem.loadv m0 a v = Some (decode_val m0 l)).
        { iClear "SZ CONC ALLOCATED". unfold points_to. des_ifs_safe.
          iDestruct "PTRTO" as "[SZ PTRTO]". iDestruct "PTRTO" as (ofs) "[A B]".
          iDestruct "A" as "[PTRTO LEN]". iDestruct "PTRTO" as "[PTRTO OFS2]".
          iAssert (⌜i = ofs⌝)%I with "[OFS OFS2]" as "%".
          { unfold has_offset. rewrite Heq. iDestruct "OFS" as "[OFS OFS']".
            iApply _has_offset_unique. iFrame. }
          subst i. Local Transparent Mem.load. des_ifs.
          - unfold _has_offset. des_ifs. iDestruct "OFS2" as "[_ EXFALSO]". clarify.
          (* Long *)
          - mAssertPure (Archi.ptr64 = true).
            { unfold _has_offset. des_ifs. }
            (* TODO : make lemmas for mAsserts *)
            rename PURE into SF. unfold Mem.loadv. rewrite SF.
            (* mAssertPure (exists base, a2 (Some b) = OneShot.white base). *)
            (* { unfold has_offset. des_ifs. iDestruct "OFS" as "[OWNOFS OFS]". *)
            (*   unfold _has_offset. rewrite SF. simpl. iDestruct "OFS" as "[HASSZ BASE]". *)
            (*   iDestruct "BASE" as (a4) "[BASE %]". des. *)
            (*   Local Transparent _has_base. specialize (SIM_CONC (Some b)). ss. *)
            (*   inv SIM_CONC; et. iCombine "CONC BASE" as "BASE". do 2 ur. iOwnWf "BASE". *)
            (*   rewrite ! URA.unfold_wf in H3. ss. specialize (H3 (Some b)). rewrite RES in H3. *)
            (*   rewrite Heq0 in H3. ss. des_ifs; ur in H3; clarify. } *)
            (* destruct PURE as [base BASE]. specialize (SIM_CONC (Some b)). ss. *)
            (* inv SIM_CONC; rewrite BASE in RES; clarify. *)
            mAssertPure (Mem.ptr2int b (Ptrofs.unsigned ofs) a = Some (Int64.unsigned i)).
            { unfold has_offset. des_ifs. iDestruct "OFS" as "[OWNOFS OFS]".
              unfold _has_offset. rewrite SF. simpl. iDestruct "OFS" as "[HASSZ BASE]".
              iDestruct "BASE" as (a4) "[BASE %]". des.
              Local Transparent _has_base. specialize (SIM_CONC (Some b)). ss.
              inv SIM_CONC; ss.
              2:{ iCombine "CONC BASE" as "AAA". ur. iOwnWf "AAA".
                  ur in H3. specialize (H3 (Some b)). ss. rewrite RES in H3. ss.
                  rewrite Heq0 in H3. ss. des_ifs. ur in H3. clarify. }
              iAssert (⌜a4 = base⌝)%I with "[CONC BASE]" as "%".
              { iCombine "CONC BASE" as "CONC2". iOwnWf "CONC2".
                ur in H3. specialize (H3 (Some b)). rewrite RES in H3. rewrite Heq0 in H3. ss.
                des_ifs. eapply OneShot.oneshot_degen in H3. et. }
              subst a4. unfold Mem.ptr2int. rewrite <- H7. ss. iPureIntro. f_equal.
              unfold Ptrofs.sub. ss. admit "mod". }
            mAssertPure (Mem.valid_pointer a b (Ptrofs.unsigned ofs) = true).
            { unfold has_offset. des_ifs. iDestruct "OFS" as "[LIVE OFS]".
              specialize (SIM_ALLOC b). admit "". }
            mAssertPure (Mem.denormalize (Int64.unsigned i) a = Some (b, Ptrofs.unsigned ofs)).
            { iPureIntro. eapply Mem.ptr2int_to_denormalize; eauto. eapply Ptrofs.unsigned_range_2. }
            rewrite PURE3. ss.
            assert (Mem.valid_access a m0 b (Ptrofs.unsigned ofs) Readable).
            { admit "". }
            iPureIntro. unfold Mem.load. des_ifs. admit "".
          (* Pointer *)
          - iAssert (⌜b = b0 /\ i = ofs⌝)%I with "[SZ OFS2]" as "%".
            { unfold _has_offset. rewrite Heq. iDestruct "OFS2" as "[SZ1 %]".
              des; clarify. }
            des. subst b0 i.
            (* iAssert (⌜i = ofs⌝)%I with "[OFS OFS2]" as "%". *)
            (* { unfold has_offset. rewrite Heq. iDestruct "OFS" as "[OFS OFS']". *)
            (*   iApply _has_offset_unique. iFrame. } *)
            (* subst i. *)
            iCombine "CNT PTRTO" as "PTRTO2". iOwnWf "PTRTO2". clear - PURE1 PURE2 H3 SIM_CNT.
            dup H3. eapply Auth.auth_included in H3. des. eapply pw_extends in H3. r in H3.
            specialize (H3 b). eapply pw_extends in H3. r in H3.
            iDestruct "LEN" as "%". iDestruct "B" as "%".
            iPureIntro. unfold Mem.loadv, Mem.load.
            assert (Mem.valid_access a m0 b (Ptrofs.unsigned ofs) Readable).
            { split.
              (* range perm *)
              - r. i. specialize (SIM_CNT b ofs0). exploit SIM_CNT; eauto.
                { destruct ofs; ss. lia. }
                i. specialize (H3 ofs0). unfold __points_to in H3. case_points_to; try lia.
                + ss. des_ifs.
                  2:{ rewrite nth_error_None in Heq. lia. }
                  apply Consent.extends in H3; eauto.
                  2:{ eapply URA.wf_mon in H4. ur in H4. des. ur in H9. spc H9. ur in H9.
                      eauto. }
                  rr in H3. des. inv x0; ss.
                  3:{ rewrite <- H11 in H9. clarify. }
                  * unfold Mem.perm. rewrite PERM. ss.
                  * unfold Mem.perm. rewrite PERM. eapply perm_order_trans; eauto. eapply perm_W_R.
                + clear - PURE1 H7 g. exfalso. rewrite size_chunk_conv in H7. lia.
              (* alignement *)
              - eapply Z.divide_transitive; et. eapply align_size_chunk_divides; et. }
            des_ifs. admit "". }
        rename PURE into LOAD. rewrite LOAD. steps. hret _; ss.
        iModIntro. iSplitR "PTRTO OFS"; cycle 1.
        (* post condition *)
        { iSplitL; eauto. iExists (decode_val m0 l). iFrame. iPureIntro. esplits; eauto. }
        (* wf *)
        { iExists _, _, _, _, _.
          iSplitR "SZ"; et. iSplitR "CONC"; et. iSplitR "ALLOCATED"; et. } } } *)
  Admitted.

  Lemma sim_store :
    sim_fnsem wf top2
      ("store", fun_to_tgt "Mem" (to_stb []) (mk_pure store_spec))
      ("store", cfunU storeF).
  Proof.
  Admitted.

  Lemma sim_sub_ptr :
    sim_fnsem wf top2
      ("sub_ptr", fun_to_tgt "Mem" (to_stb []) (mk_pure sub_ptr_spec))
      ("sub_ptr", cfunU sub_ptrF).
  Proof.
  Admitted.

  Lemma sim_cmp_ptr :
    sim_fnsem wf top2
      ("cmp_ptr", fun_to_tgt "Mem" (to_stb []) (mk_pure cmp_ptr_spec))
      ("cmp_ptr", cfunU cmp_ptrF).
  Proof.
  Admitted.

  Lemma sim_non_null :
    sim_fnsem wf top2
      ("non_null?", fun_to_tgt "Mem" (to_stb []) (mk_pure non_null_spec))
      ("non_null?", cfunU non_nullF).
  Proof.
  Admitted.

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
  Admitted.

  Lemma sim_capture :
    sim_fnsem wf top2
      ("capture", fun_to_tgt "Mem" (to_stb []) (mk_pure capture_spec))
      ("capture", cfunU captureF).
  Proof.
  Admitted.

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
