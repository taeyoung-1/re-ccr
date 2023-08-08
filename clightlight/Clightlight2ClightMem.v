From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Values Maps.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Clight_Mem0.

Require Import ConvC2ITree.
Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightArith.

From compcert Require Import Clight Clightdefs.

Set Implicit Arguments.


Section MEM.

  Context `{Σ: GRA.t}.

  Import List.

  Lemma map_blk_after_init :
    forall defs blk
      (ALLOCED : S (length (get_sk defs)) <= Pos.to_nat blk),
      (<<ALLOCMAP: map_blk defs blk = Pos.of_nat ((List.length defs - List.length (get_sk defs)) + (Pos.to_nat blk))>>).
  Proof. unfold map_blk. i. des_ifs. Qed.

  Lemma fold_left_prop :
    forall A B C (f: A -> C) (g: A -> B -> A) (h: C -> C) l i
      (COMM: forall a b, f (g a b) = h (f a)),
      f (fold_left g l i) = fold_left (fun x _ => h x) l (f i).
  Proof.
    i. do 2 rewrite <- fold_left_rev_right. set (rev l) as l'. clearbody l'. induction l'; ss.
    rewrite COMM. f_equal. et.
  Qed.
  
  Variable defs : list (ident * globdef fundef Ctypes.type).

  Hypothesis defs_ident_from_string :
    forall p gd , In (p, gd) defs -> exists s, ident_of_string s = p.
  
  Hypothesis def_ident_nodup : NoDup (map (fun '(id, _) => id) defs).

  Lemma get_sk_incl :
    forall s a , In (s, a) (get_sk defs) -> exists gd, In (ident_of_string s, gd) defs.
  Proof.
    clear def_ident_nodup. i. depgen s. revert a. induction defs; i.
    - inv H.
    - destruct a.
      assert (HINT: exists s, ident_of_string s = i).
      { eapply defs_ident_from_string. instantiate (1 := g). ss. auto. }
      des. symmetry in HINT. subst. ss. des_ifs; ss.
      + rewrite string_of_ident_of_string in H. des.
        { inv H. et. } { apply IHl in H. { des. et. } { i. eapply defs_ident_from_string. et. } }
      + apply IHl in H. { des. et. } { i. eapply defs_ident_from_string. et. } 
      + apply IHl in H. { des. et. } { i. eapply defs_ident_from_string. et. } 
      + rewrite string_of_ident_of_string in H. des.
        { inv H. et. } { apply IHl in H. { des. et. } { i. eapply defs_ident_from_string. et. } }
  Qed.

  Local Transparent Sk.load_skenv.

  Lemma map_blk_global_region :
    forall blk
      (SRC_GLOBAL: S (length (get_sk defs)) > Pos.to_nat blk),
      (<<TGT_GLOBAL: Pos.to_nat (map_blk defs blk) < S (List.length defs)>>).
  Proof.
    i. unfold map_blk. 
    change (Genv.add_globals _ defs) with (Genv.globalenv (AST.mkprogram defs (map fst defs) xH)).
    des_ifs; try nia; red.
    - clear - Heq0. 
      unfold Genv.find_symbol in *. apply Genv.genv_symb_range in Heq0.
      replace (Genv.genv_next _) with (Pos.of_nat (S (List.length defs))) in Heq0.
      2:{ clear. unfold Genv.globalenv. unfold Genv.add_globals.
          rewrite fold_left_prop with (h := Pos.succ); et. 
          induction defs; try (ss; nia). ss. rewrite IHl.
          clear. do 2 rewrite <- fold_left_rev_right. set (rev l) as d'. clearbody d'.
          induction d'; ss; nia. }
      set (S _) as n in *. assert (n > 0) by now ss; nia. clearbody n. clear -Heq0 H. 
      gen b. induction H; i; try nia.
      + inv Heq0. unfold Pos.compare in *. ss. des_ifs.
      + rewrite Nat2Pos.inj_succ in Heq0; try nia. apply Coqlib.Plt_succ_inv in Heq0.
        des; try (subst; nia). apply IHle in Heq0. nia.
    - unfold Sk.load_skenv in Heq. ss. uo. des_ifs_safe.
      apply nth_error_In in Heq. apply get_sk_incl in Heq. des.
      set (AST.mkprogram _ _ _) as prog in Heq0.
      change defs with (prog_defs prog) in Heq.
      apply Genv.find_symbol_exists in Heq. des. clarify.
    - unfold Sk.load_skenv in Heq. ss. uo. des_ifs. apply nth_error_None in Heq1. nia.
  Qed.

  Lemma map_blk_inj :
    forall b1 b2, <<INJ: map_blk defs b1 = map_blk defs b2 -> b1 = b2>>.
  Proof.
    i.
    assert (LEN: length (get_sk defs) <= length defs).
    { clear. induction defs; et. simpl. des_ifs; ss; try nia. }
    red. i. dup H.
    unfold map_blk in H0.
    destruct (ge_dec (Pos.to_nat b1) _) in H0; destruct (ge_dec (Pos.to_nat b2) _) in H0; try nia; clear H0.
    - assert (contra1: Pos.to_nat b2 < S (length (get_sk defs))) by nia.
      apply map_blk_global_region in contra1. 
      assert (contra2: S (length (get_sk defs)) <= Pos.to_nat b1) by nia.
      apply map_blk_after_init in contra2. rewrite H in contra2. red in contra2. red in contra1.
      nia. 
    - assert (contra1: Pos.to_nat b1 < S (length (get_sk defs))) by nia.
      apply map_blk_global_region in contra1. 
      assert (contra2: S (length (get_sk defs)) <= Pos.to_nat b2) by nia.
      apply map_blk_after_init in contra2. rewrite H in contra1. red in contra2. red in contra1.
      nia. 
    - (* may not needed *)
      unfold map_blk in H. destruct (ge_dec (Pos.to_nat b1) _) in H; destruct (ge_dec (Pos.to_nat b2) _) in H; try nia.
      assert (H1: Init.Nat.pred (Pos.to_nat b1) < length (get_sk defs)) by nia.
      assert (H2: Init.Nat.pred (Pos.to_nat b2) < length (get_sk defs)) by nia.
      apply nth_error_Some in H1.
      apply nth_error_Some in H2.
      unfold Sk.load_skenv in *. uo. ss.
      dup H1. dup H2. rename H3 into H4. rename H0 into H3.
      destruct (nth_error _) eqn: E1 in H3; clarify. dup E1. rename E0 into E3. apply nth_error_In in E1.
      destruct (nth_error _) eqn: E2 in H4; clarify. dup E2. rename E0 into E4. apply nth_error_In in E2.
      destruct p. destruct p0.
      apply get_sk_incl in E1.
      apply get_sk_incl in E2.
      rewrite E3 in H. rewrite E4 in H.
      change defs with (prog_defs (AST.mkprogram defs (map fst defs) xH)) in E1.
      change defs with (prog_defs (AST.mkprogram defs (map fst defs) xH)) in E2.
      des. apply Genv.find_symbol_exists in E1. apply Genv.find_symbol_exists in E2.
      des. unfold Genv.globalenv in *. ss. des_ifs.
      (* TODO: from here, proof with noDup is trivial *)
      (* noDup property is needed to satisfy one-to-one correspondence in global region *)
      Admitted.

(* 

  Variable src : Imp.programL.
  Variable m : Mem.t.
  Variable tm : Mem.mem.
  Context {MM: match_mem src m tm}.
  Context {WFPROG: (incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))}.
  Context {WFSK: Sk.wf src.(defsL)}.
  Context {COMP : exists tgt, compile src = OK tgt}.

  Lemma match_mem_alloc
        n m2 blk tm2 tblk
        (SMEM: (blk, m2) = Mem.alloc m n)
        (TMEM: (tm2, tblk) = Memory.Mem.alloc tm (- size_chunk Mptr) (map_ofs n))
    :
      (<<MM2: match_mem src m2 tm2>>).
  Proof.
    inv MM. inv SMEM. split; i; ss; try split.
    - lia.
    - hexploit Mem.nextblock_alloc; eauto. i. rewrite H. rewrite NBLK.
      hexploit map_blk_after_init.
      { eauto. }
      { instantiate (1:= Mem.nb m). lia. }
      hexploit map_blk_after_init.
      { eauto. }
      { instantiate (1:= S (Mem.nb m)). lia. }
      i. rewrite H1. rewrite H0. lia.
    - rename H into SMEM. pose (NPeano.Nat.eq_dec (Mem.nb m) blk) as BLK. destruct BLK.
      + clarify; ss. unfold update in SMEM. des_ifs. clear e. des. clarify. ss. rewrite <- NBLK.
        rewrite andb_true_iff in Heq. des. rewrite Z.leb_le in Heq. rewrite Z.ltb_lt in Heq0.
        rename Heq into LB. rename Heq0 into UB.
        hexploit Mem.load_alloc_same'; ss; eauto.
        { unfold size_chunk. des_ifs. instantiate (1:=map_ofs ofs). unfold map_ofs. nia. }
        { instantiate (1:=Mint64). unfold size_chunk. des_ifs. unfold map_ofs in *. nia. }
        { unfold align_chunk. des_ifs. unfold map_ofs. unfold Z.divide. exists ofs. nia. }
        i. hexploit Mem.alloc_result; eauto. i. clarify.
      + unfold update in SMEM. des_ifs. clear n0. rename n1 into BLK. apply MMEM in SMEM. des.
        hexploit Mem.load_alloc_other; eauto.
    - rename H into SMEM. pose (NPeano.Nat.eq_dec (Mem.nb m) blk) as BLK. destruct BLK.
      + clarify; ss. unfold update in SMEM. des_ifs. clear e. des. clarify. rewrite <- NBLK.
        rewrite andb_true_iff in Heq. des. rewrite Z.leb_le in Heq. rewrite Z.ltb_lt in Heq0.
        rename Heq into LB. rename Heq0 into UB.
        hexploit Mem.valid_access_alloc_same; eauto.
        { unfold size_chunk. des_ifs. instantiate (1:=map_ofs ofs). unfold map_ofs. nia. }
        { instantiate (1:=Mint64). unfold size_chunk. des_ifs. unfold map_ofs in *. nia. }
        { unfold align_chunk. des_ifs. unfold map_ofs. unfold Z.divide. exists ofs. nia. }
        i. hexploit Mem.alloc_result; eauto. i. clarify. hexploit Mem.valid_access_freeable_any; eauto.
      + unfold update in SMEM. des_ifs. clear n0. rename n1 into BLK. apply MMEM in SMEM. des.
        hexploit Mem.valid_access_alloc_other; eauto.
  Qed.

  Lemma match_mem_malloc
        n m2 blk tm2
        (SMEM: (blk, m2) = Mem.alloc m n)
        (TMEM : Memory.Mem.store Mptr (fst (Memory.Mem.alloc tm (- size_chunk Mptr) (map_ofs n)))
                                 (snd (Memory.Mem.alloc tm (- size_chunk Mptr) (map_ofs n))) (- size_chunk Mptr)
                                 (Values.Vlong (Int64.repr (map_ofs n))) = Some tm2)
    :
      <<MM2: match_mem src m2 tm2>>.
  Proof.
    unfold map_ofs in *. remember (Memory.Mem.alloc tm (- size_chunk Mptr) (8 * n)) as tm1. destruct tm1 as [tm1 tblk].
    hexploit match_mem_alloc; eauto. i. inv H. split; i; try split.
    - lia.
    - rewrite <- NBLK. eapply Mem.nextblock_store; eauto.
    - rename H into SRCM. pose (NPeano.Nat.eq_dec blk blk0) as BLK. destruct BLK.
      + clarify; ss. unfold map_ofs in *. unfold size_chunk in *. des_ifs; ss.
        pose (Z_le_gt_dec 0 (8 * ofs)) as OFS. destruct OFS.
        * erewrite Mem.load_store_other; eauto. apply MMEM in SRCM. des. eauto.
        * depgen SMEM. depgen g. depgen SRCM. clear. i. unfold Mem.alloc in SMEM. inv SMEM. ss.
          unfold update in SRCM. des_ifs. nia.
      + erewrite Mem.load_store_other; eauto.
        * apply MMEM in SRCM. des; eauto.
        * left. sym in Heqtm1. apply Mem.alloc_result in Heqtm1. clarify. ss.
          unfold Mem.alloc in SMEM. inv SMEM. ss. inv MM. rewrite NBLK0. depgen n0. depgen map_blk_inj.
          ii. apply map_blk_inj in H; eauto. 
    - apply MMEM in H; des. hexploit Mem.store_valid_access_1; eauto. 
  Qed.
*)

  Local Transparent Mem.free.

  Lemma match_mem_free m tm b lo hi m'
        (SMEM: Mem.free m b lo hi = Some m')
        (MM_PRE: match_mem defs m tm)
    :
    exists tm',
        (<<TMEM: Mem.free tm (map_blk defs b) lo hi = Some tm'>>) /\
        (<<MM_POST: match_mem defs m' tm'>>).
  Proof.
    inv MM_PRE. unfold Mem.free in *. eexists. split. 
    - des_ifs. exfalso. apply n. unfold Mem.range_perm, Mem.perm in *.
      i. rewrite <- MEM_PERM. et.
    - des_ifs. unfold Mem.unchecked_free. econs; et.
      ss. i. set (Pos.eq_dec b b0) as x. destruct x.
      + subst. repeat rewrite PMap.gss. repeat rewrite MEM_PERM. et.
      + rewrite PMap.gso by et.
        assert (map_blk defs b <> map_blk defs b0).
        { red. i. apply n. apply map_blk_inj in H; et. }
        rewrite PMap.gso; et.
  Qed.

  Lemma match_mem_free_list m tm l m'
        (SMEM: Mem.free_list m l = Some m')
        (MM_PRE: match_mem defs m tm)
    :
    exists tm',
        (<<TMEM: Mem.free_list tm (map (fun '(b, lo, hi) => (map_blk defs b, lo, hi)) l) = Some tm'>>) /\
        (<<MM_POST: match_mem defs m' tm'>>).
  Proof.
    depgen m. revert m' tm. induction l; i; ss; clarify.
    - eexists; et.
    - des_ifs_safe. hexploit match_mem_free; et. i. des. rewrite TMEM.
      hexploit IHl; et.
  Qed.

(*
  Lemma match_mem_store
        blk ofs v m2
        (SMEM: Mem.store m blk ofs v = Some m2)
    :
      exists tm2,
        ((<<TMEM: Memory.Mem.store Mint64 tm (map_blk src blk) (map_ofs ofs) (map_val src v) = Some tm2>>) /\
        (<<MM2: match_mem src m2 tm2>>)).
  Proof.
    inv MM. unfold Mem.store in SMEM. des_ifs. hexploit MMEM; eauto. i; des.
    hexploit (Mem.valid_access_store tm Mint64 (map_blk src blk) (map_ofs ofs) (map_val src v)); eauto.
    i. dependent destruction X. rename x into tm2. rename e into TGTM2. exists tm2. split; auto. try split; i; try split; ss; eauto.
    - erewrite Mem.nextblock_store; eauto.
    - des_ifs.
      + des; clarify; ss. bsimpl. des. apply sumbool_to_bool_true in Heq0. apply sumbool_to_bool_true in Heq1. clarify.
        erewrite Mem.load_store_same; eauto. unfold map_val. ss. des_ifs.
      + bsimpl. des.
        * apply sumbool_to_bool_false in Heq0. hexploit Mem.load_store_other; eauto.
          { left. instantiate (1:= map_blk src blk0). ii. apply map_blk_inj in H0; eauto. }
          i. erewrite H0. apply MMEM in H. des. eauto.
        * apply sumbool_to_bool_false in Heq0. hexploit Mem.load_store_other; eauto.
          2:{ i. erewrite H0. apply MMEM in H. des. eauto. }
          right. ss. unfold map_ofs in *. lia.
    - des_ifs.
      + des; clarify; ss. bsimpl. des. apply sumbool_to_bool_true in Heq0. apply sumbool_to_bool_true in Heq1. clarify.
        split; auto. eapply Mem.store_valid_access_1; eauto.
      + bsimpl. des.
        * apply sumbool_to_bool_false in Heq0. apply MMEM in H; des. split; auto. eapply Mem.store_valid_access_1; eauto.
        * apply sumbool_to_bool_false in Heq0. apply MMEM in H; des. split; auto. eapply Mem.store_valid_access_1; eauto.
  Qed.

  Lemma valid_ptr_contra
        blk ofs
        (WFOFS: modrange_64 (scale_ofs ofs))
        (SRC: Mem.valid_ptr m blk ofs = true)
        (TGT: Mem.valid_pointer tm (map_blk src blk) (Ptrofs.unsigned (Ptrofs.repr (map_ofs ofs))) = false)
    :
      False.
  Proof.
    unfold Mem.valid_ptr in SRC. unfold is_some in SRC. des_ifs.
    inv MM. apply MMEM in Heq. des. clear MMEM. unfold map_ofs in *.
    unfold scale_ofs in WFOFS.
    rewrite unwrap_Ptrofs_repr_z in TGT; try nia; auto.
    rename TGT into CONTRA.
    match goal with [ CONTRA: ?vp = false |- _ ] => assert (CONTRA2: vp = true) end.
    { rewrite Mem.valid_pointer_nonempty_perm. eapply Mem.valid_access_perm in TVALID.
      hexploit Mem.perm_implies; eauto. econs. }
    clarify.
  Qed.

  Lemma valid_ptr_wf_ofs
        blk ofs
        (VACC : Mem.valid_ptr m blk ofs = true)
    :
      (0 <= ofs)%Z.
  Proof.
    unfold Mem.valid_ptr in VACC. unfold is_some in VACC. des_ifs. inv MM. eapply MMEM in Heq; des; eauto.
  Qed.

  Lemma match_mem_cmp
        a b tf
        (WFA: wf_val a)
        (WFB: wf_val b)
        (SRCCMP: vcmp m a b = Some tf)
    :
      Values.Val.cmplu (Mem.valid_pointer tm) Ceq (map_val src a) (map_val src b) =
      if (tf) then Some (Values.Vtrue) else Some (Values.Vfalse).
  Proof.
    destruct a eqn:DESA; destruct b eqn:DESB; destruct tf; clarify; unfold vcmp in SRCCMP; des_ifs.
    - apply sumbool_to_bool_true in H0. clarify; ss.
      unfold Values.Val.cmplu. ss. unfold Values.Val.of_bool. rewrite Int64.eq_true. ss.
    - apply sumbool_to_bool_false in H0. clarify; ss.
      unfold Values.Val.cmplu. ss. unfold Values.Val.of_bool. rewrite Int64.signed_eq.
      unfold_intrange_64. bsimpl. des.
      apply sumbool_to_bool_true in WFA.
      apply sumbool_to_bool_true in WFA0.
      apply sumbool_to_bool_true in WFB.
      apply sumbool_to_bool_true in WFB0.
      rewrite! Int64.signed_repr.
      2,3: unfold_Int64_min_signed; unfold_Int64_max_signed; try nia.
      des_ifs. apply Coqlib.proj_sumbool_true in Heq; clarify.
    - clear SRCCMP. bsimpl. des. apply sumbool_to_bool_true in Heq0. clarify.
      unfold Values.Val.cmplu. ss. des_ifs. bsimpl. des. exfalso. eapply valid_ptr_contra; eauto.
    - clear SRCCMP. bsimpl. des. apply sumbool_to_bool_true in Heq0. clarify.
      unfold Values.Val.cmplu. ss. des_ifs. bsimpl. des. exfalso. eapply valid_ptr_contra; eauto.
    - bsimpl. des. apply sumbool_to_bool_true in H0; clarify. apply sumbool_to_bool_true in H1; clarify; clarify.
      clear Heq. unfold Values.Val.cmplu. ss. des_ifs; bsimpl; des.
      all: try (rewrite Ptrofs.eq_true; ss).
      all: exfalso; eapply valid_ptr_contra; eauto.
    - bsimpl; des.
      + apply sumbool_to_bool_false in H0. rename H0 into BLK. unfold Values.Val.cmplu. ss. des_ifs.
        1,2: apply map_blk_inj in e; clarify.
        bsimpl. des.
        { pose (valid_ptr_contra _ _ WFA Heq Heq2). clarify. }
        { pose (valid_ptr_contra _ _ WFB Heq0 Heq2). clarify. }
      + apply sumbool_to_bool_false in H0. rename H0 into OFS. unfold Values.Val.cmplu. ss. des_ifs.
        { apply map_blk_inj in e; clarify. ss.
          unfold Ptrofs.eq. hexploit (valid_ptr_wf_ofs _ _ Heq); i. hexploit (valid_ptr_wf_ofs _ _ Heq0); i.
          unfold map_ofs in *. rewrite! unwrap_Ptrofs_repr_z; try nia; eauto. erewrite Coqlib.zeq_false; try lia. ss. }
        { bsimpl; des.
          - pose (valid_ptr_contra _ _ WFA Heq Heq2). clarify.
          - pose (valid_ptr_contra _ _ WFB Heq0 Heq2). clarify. }
        { bsimpl; des.
          - pose (valid_ptr_contra _ _ WFA Heq Heq2). clarify.
          - pose (valid_ptr_contra _ _ WFB Heq0 Heq2). clarify. }
  Qed. *)

End MEM.
