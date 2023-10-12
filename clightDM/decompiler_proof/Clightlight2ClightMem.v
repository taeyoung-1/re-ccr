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

  (* Lemma map_blk_after_init :
    forall sk defs blk
      (ALLOCED : Pos.of_succ_nat (length sk) <= blk),
      (<<ALLOCMAP: map_blk sk defs blk = Pos.of_nat ((List.length defs - List.length sk) + (Pos.to_nat blk))>>).
  Proof.
    unfold map_blk. i. des_ifs; rewrite Pos.leb_gt in Heq; nia. Qed.

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
    forall p , In p (map fst defs) -> exists s, ident_of_string s = p.
  
  Hypothesis def_ident_nodup : NoDup (map fst defs). *)

  (* Lemma get_sk_incl :
    forall s l, (forall p, In p (map fst l) -> exists s, ident_of_string s = p) 
                  -> In s (map fst (get_sk l)) 
                  -> In (ident_of_string s) (map fst l).
  Proof.
    i. induction l; et. ss. des_ifs. 
    - ss. des.
      + clarify. left. hexploit H; et. i. des. rewrite <- H.
        rewrite string_of_ident_of_string. et.
      + hexploit IHl; et.
    - ss. hexploit IHl; et. 
    - ss. des.
      + clarify. left. hexploit H; et. i. des. rewrite <- H.
        rewrite string_of_ident_of_string. et.
      + hexploit IHl; et.
  Qed.

  Lemma get_sk_NoDup : forall l, 
                      (forall p, In p (map fst l) -> exists s, ident_of_string s = p) ->
                      NoDup (map fst l) -> NoDup (map fst (get_sk l)).
  Proof.
    induction l; try econs. i. ss. des_ifs.
    - ss. inv H. econs. 
      + red. i. eapply H3. hexploit H; et. i. des. subst. 
        rewrite string_of_ident_of_string in H. eapply get_sk_incl; et.
      + eapply IHl; et.
    - ss. inv H. eapply IHl; et.
    - ss. inv H. econs. 
      + red. i. eapply H3. hexploit H; et. i. des. subst. 
        rewrite string_of_ident_of_string in H. eapply get_sk_incl; et.
      + eapply IHl; et.
  Qed. *)

  Local Transparent Sk.load_skenv.

  Local Open Scope positive.
  Lemma map_blk_local_region :
    forall sk tge blk
      (ALLOCED : Pos.of_succ_nat (length sk) <= blk),
      (<<ALLOCMAP: tge.(Genv.genv_next) <= map_blk sk tge blk>>).
  Proof.
    i. red. unfold map_blk. 
    set (Z.add _ _) as t1. 
    assert (t1 > 0)%Z by now unfold t1; nia. 
    destruct t1 eqn: E3; try nia. 
    des_ifs; try rewrite Pos.leb_le in Heq; try rewrite Pos.leb_gt in Heq; try nia.
  Qed.

  Lemma map_blk_global_region :
    forall sk tge blk
      (SRC_GLOBAL: not (Pos.of_succ_nat (length sk) <= blk))
      (MGE : match_ge sk tge),
      (<<TGT_GLOBAL: map_blk sk tge blk < tge.(Genv.genv_next)>>).
  Proof.
    i. inv MGE. red. unfold map_blk. des_ifs; try nia.
    - eapply Genv.genv_symb_range. et.
    - apply Sk.load_skenv_wf in WFSK. unfold SkEnv.wf in WFSK. apply WFSK in Heq. rewrite <- (string_of_ident_of_string s) in Heq. apply MGE0 in Heq. clarify.
    - assert (H0: (Init.Nat.pred (Pos.to_nat blk) < length sk)%nat) by nia.
      apply nth_error_Some in H0. unfold Sk.load_skenv in Heq. ss. uo. des_ifs.
  Qed.

  Local Open Scope Z.
  Lemma map_blk_inj :
    forall sk tge b1 b2 (MGE: match_ge sk tge),
    <<INJ: map_blk sk tge b1 = map_blk sk tge b2 -> b1 = b2>>.
  Proof.
    i. red. i. dup H. rename H0 into T.
    unfold map_blk in H.
    destruct (le_dec _ _) in H; 
     destruct (le_dec _ _) in H.
    - set (Z.add _ _) as t1 in H. set (Z.add _ _) as t2 in H.
      assert (t1 > 0) by now unfold t1; nia. 
      assert (t2 > 0) by now unfold t2; nia. 
      destruct t1 eqn: E3; destruct t2 eqn: E4; try nia.
    - eapply map_blk_global_region in n; et. apply map_blk_local_region with (tge := tge) in l. red in n. red in l. nia.
    - eapply map_blk_global_region in n; et. apply map_blk_local_region with (tge := tge) in l. red in n. red in l. nia.
    - inv MGE. 
      assert (H0: (Init.Nat.pred (Pos.to_nat b1) < length sk)%nat) by nia.
      assert (H1: (Init.Nat.pred (Pos.to_nat b2) < length sk)%nat) by nia.
      apply nth_error_Some in H0.
      apply nth_error_Some in H1.
      destruct (nth_error _) eqn: T1 in H0; clarify.
      destruct (nth_error _) eqn: T2 in H1; clarify. 
      clear H0 H1.
      destruct (SkEnv.blk2id _ _) eqn: H0 in H.
      2:{ unfold Sk.load_skenv in *. ss. uo. des_ifs. }
      destruct (SkEnv.blk2id _ _) eqn: H1 in H.
      2:{ unfold Sk.load_skenv in *. ss. uo. des_ifs. }
      clear T1 T2. 
      apply Sk.load_skenv_wf in WFSK. red in WFSK. unfold SkEnv.wf in WFSK. 
      apply WFSK in H0. apply WFSK in H1.
      rewrite <- (string_of_ident_of_string s) in H0.
      rewrite <- (string_of_ident_of_string s0) in H1.
      dup H0. dup H1.
      apply MGE0 in H2. apply MGE0 in H3. des_ifs; clarify.
      destruct (Pos.eq_dec (ident_of_string s) (ident_of_string s0)); cycle 1.
      + hexploit Genv.global_addresses_distinct; et. clarify.
      + apply ident_of_string_injective in e. subst.
        set (Some _) as t1 in H0.
        set (Some _) as t2 in H1.
        assert (t1 = t2) by now rewrite <- H0; et.
        unfold t1, t2 in H. clearbody t1 t2. clarify.
        nia.
  Qed.



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
      i. rewrite H1. rewrite H. lia.
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

  Local Transparent Mem.alloc.
  Local Transparent Mem.free.
  Local Transparent Mem.load.
  Local Transparent Mem.store.
  Local Transparent Mem.loadbytes.
  Local Transparent Mem.storebytes.


  Lemma match_mem_free m tm b lo hi m' sk tge
        (SMEM: Mem.free m b lo hi = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
    exists tm',
        (<<TMEM: Mem.free tm (map_blk sk tge b) lo hi = Some tm'>>) /\
        (<<MM_POST: match_mem sk tge m' tm'>>).
  Proof.
    inv MM_PRE. unfold Mem.free in *. eexists. split. 
    - des_ifs. exfalso. apply n. unfold Mem.range_perm, Mem.perm in *.
      i. rewrite <- MEM_PERM. et.
    - des_ifs. unfold Mem.unchecked_free. econs; et.
      ss. i. set (Pos.eq_dec b b0) as x. destruct x.
      + subst. repeat rewrite PMap.gss. repeat rewrite MEM_PERM. et.
      + rewrite PMap.gso by et.
        assert (map_blk sk tge b <> map_blk sk tge b0).
        { red. i. apply n. apply map_blk_inj in H; et. }
        rewrite PMap.gso; et.
  Qed.

  Lemma match_mem_free_list m tm l m' sk tge
        (SMEM: Mem.free_list m l = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
    exists tm',
        (<<TMEM: Mem.free_list tm (map (fun '(b, lo, hi) => (map_blk sk tge b, lo, hi)) l) = Some tm'>>) /\
        (<<MM_POST: match_mem sk tge m' tm'>>).
  Proof.
    depgen m. revert m' tm. induction l; i; ss; clarify.
    - eexists; et.
    - des_ifs_safe. hexploit match_mem_free; et. i. des. rewrite TMEM.
      hexploit IHl; et.
  Qed.

  Lemma match_mem_getN f (c d: ZMap.t memval) n p
      (MM: forall i mv, c !! i = mv -> d !! i = f mv)
    :
      Mem.getN n p d = map f (Mem.getN n p c).
  Proof.
    revert p. induction n; i; ss.
    rewrite IHn. f_equal. erewrite <- MM; try reflexivity.  
  Qed.

  Lemma match_proj_bytes sk tge l : proj_bytes (map (map_memval sk tge) l) = proj_bytes l. 
  Proof. induction l; ss. rewrite IHl. destruct a; ss. Qed.
  
  Lemma match_check_value n q v sk tge l 
        (MGE: match_ge sk tge)
    : check_value n (map_val sk tge v) q (map (map_memval sk tge) l) = check_value n v q l.
  Proof.
    revert q v l. induction n; i.
    - ss. des_ifs.
    - ss. des_ifs. ss. clarify. rewrite IHn. repeat f_equal.
      destruct v; destruct v1; ss.
      destruct (Val.eq (Vptr b i) (Vptr b0 i0));
        destruct (Val.eq _ _); ss; clarify.
      apply map_blk_inj in H1; et. subst. clarify.
  Qed.

  Lemma decode_map_comm sk tge chunk l
        (MGE: match_ge sk tge)
    : 
      decode_val chunk (map (map_memval sk tge) l) = map_val sk tge (decode_val chunk l).
  Proof.
    induction l.
    - ss. unfold decode_val. des_ifs.
    - ss. unfold decode_val. destruct a.
      + ss. des_ifs.
      + ss. rewrite match_proj_bytes. des_ifs.
      + rewrite <- match_proj_bytes with (sk := sk) (l := Fragment v q n :: l) (tge := tge). des_ifs.
        * unfold proj_value. rewrite <- match_check_value with (sk := sk) at 1; et.
          des_ifs; ss; clarify. destruct v; et.
        * unfold proj_value. rewrite <- match_check_value with (sk := sk) at 1; et.
          des_ifs; ss; clarify. destruct v; et.
        * unfold proj_value. rewrite <- match_check_value with (sk := sk) at 1; et.
          des_ifs; ss; clarify. 
  Qed.

  Lemma match_mem_load m tm chunk b ofs v sk tge
        (SMEM: Mem.load chunk m b ofs = Some v)
        (MGE: match_ge sk tge)
        (MM: match_mem sk tge m tm)
    :
        Mem.load chunk tm (map_blk sk tge b) ofs = Some (map_val sk tge v).
  Proof.
    inv MM. unfold Mem.load in *.
    des_ifs.
    - f_equal. erewrite match_mem_getN; et. apply decode_map_comm; et.
    - exfalso. apply n. unfold Mem.valid_access in *. des. split; et. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. et.
  Qed.

  Lemma zindex_surj p : exists z, p = ZIndexed.index z.
  Proof. 
    destruct p.
    - exists (Zneg p). et.
    - exists (Zpos p). et.
    - exists 0%Z. et.
  Qed.

  Lemma encode_match_comm chunk sk tge v : encode_val chunk (map_val sk tge v) = map (map_memval sk tge) (encode_val chunk v).
  Proof. destruct v; ss; des_ifs. Qed.

  Lemma setN_inside x l i c
      (IN_RANGE: (i <= x)%Z /\ (x < i + Z.of_nat (length l))%Z)
    :
      exists entry, nth_error l (Z.to_nat (x - i)%Z) = Some entry /\ ZMap.get x (Mem.setN l i c) = entry.
  Proof.
    assert (Z.to_nat (x - i)%Z < length l)%nat by nia.
    apply nth_error_Some in H. destruct (nth_error _ _) eqn: E in H; clarify.
    eexists; split; et. clear H. depgen x. revert i c m. induction l; i; ss; try nia.
    destruct (Nat.eq_dec (Z.to_nat (x - i)) 0).
    - rewrite e in *. ss. clarify. assert (x = i) by nia. rewrite H in *.
      rewrite Mem.setN_outside; try nia. apply ZMap.gss. 
    - change (a :: l) with ([a] ++ l) in E. rewrite nth_error_app2 in E; ss; try nia.
      replace (Z.to_nat (x - i) - 1)%nat with (Z.to_nat (x - (i + 1))) in E by nia.
      eapply IHl; et. nia.
  Qed.

  Lemma match_mem_alloc m tm b lo hi m' sk tge
        (SMEM: Mem.alloc m lo hi = (m', b))
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
    exists tm',
        (<<TMEM: Mem.alloc tm lo hi = (tm', map_blk sk tge b)>>) /\
        (<<MM_POST: match_mem sk tge m' tm'>>).
  Proof.
    inv MM_PRE. unfold Mem.alloc in *. clarify. eexists. split. 
    - rewrite <- NBLK. red. f_equal.
    - red. econs.
      + ss. nia.
      + ss. rewrite NBLK. unfold map_blk. des_ifs; try nia.
      + i. ss. destruct (Pos.eq_dec (Mem.nextblock m) b).
        * rewrite <- e in *. rewrite NBLK. rewrite PMap.gss in *. 
          destruct (zindex_surj ofs). rewrite H0 in *. rewrite H.
          change (_ !! _) with (ZMap.get x (ZMap.init Undef)) in H.
          rewrite ZMap.gi in H. subst. et.
        * rewrite PMap.gso in *; et. rewrite NBLK. red. red in n. revert n. i.
          apply n. eapply map_blk_inj; et. 
      + i. ss. destruct (Pos.eq_dec (Mem.nextblock m) b).
        * rewrite <- e in *. rewrite NBLK in *. do 2 rewrite PMap.gss. et. 
        * do 2 try rewrite PMap.gso; et. rewrite NBLK. red. red in n. revert n. i.
          apply n. eapply map_blk_inj; et. 
  Qed.

  Lemma match_mem_store m tm m' chunk b ofs v sk tge
        (SMEM: Mem.store chunk m b ofs v = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
      exists tm',
        <<TMEM: Mem.store chunk tm (map_blk sk tge b) ofs (map_val sk tge v) = Some tm'>> /\
        <<MM_POST: match_mem sk tge m' tm'>>.
  Proof.
    inv MM_PRE. unfold Mem.store in *.
    des_ifs.
    - eexists; split; et. econs; ss. i. destruct (zindex_surj ofs0). rewrite encode_match_comm.
      destruct (Pos.eq_dec b b0); 
        destruct ((x <? ofs) || (x >=? ofs + Z.of_nat (length (encode_val chunk v))))%Z eqn: e1.
      + rewrite e in *. rewrite PMap.gss in *.  
        rewrite H0 in *. pose proof Mem.setN_outside. unfold ZMap.get in *. 
        rewrite H1 in H; try nia. rewrite H1; et. rewrite map_length. nia.
      + rewrite e in *. rewrite PMap.gss in *. rewrite H0 in *. 
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H2 in H]; try nia. rewrite H in *. 
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H4]; try (rewrite map_length; nia).
        clear -H1 H3. rewrite nth_error_map in H3. rewrite H1 in H3. ss. clarify.
      + assert (map_blk sk tge b <> map_blk sk tge b0).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
      + assert (map_blk sk tge b <> map_blk sk tge b0).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
    - exfalso. apply n. unfold Mem.valid_access in *. des. split; et. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. et.
  Qed.

  Lemma match_mem_loadbytes m tm blk ofs n l sk tge
        (SMEM: Mem.loadbytes m blk ofs n = Some l)
        (MM: match_mem sk tge m tm)
    :
        Mem.loadbytes tm (map_blk sk tge blk) ofs n = Some (map (map_memval sk tge) l).
  Proof.
    inv MM. unfold Mem.loadbytes in *. des_ifs_safe. ss. clarify. 
    des_ifs.
    - f_equal. erewrite match_mem_getN; et.
    - exfalso. apply n0. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. et.
  Qed.

  Lemma match_mem_storebytes m tm m' blk ofs l sk tge
        (SMEM: Mem.storebytes m blk ofs l = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
      exists tm',
        <<TMEM: Mem.storebytes tm (map_blk sk tge blk) ofs (map (map_memval sk tge) l) = Some tm'>> /\
        <<MM_POST: match_mem sk tge m' tm'>>.
  Proof.
    inv MM_PRE. unfold Mem.storebytes in *. des_ifs.
    - eexists; split; et. econs; ss. i. destruct (zindex_surj ofs0). rewrite H0 in *.
      destruct (Pos.eq_dec blk b); 
        destruct ((x <? ofs) || (x >=? ofs + Z.of_nat (length l)))%Z eqn: e1.
      + rewrite e in *. rewrite PMap.gss in *.  
        pose proof Mem.setN_outside. unfold ZMap.get in *. 
        rewrite H1 in H; try nia. rewrite H1; et. rewrite map_length. nia.
      + rewrite e in *. rewrite PMap.gss in *.
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H2 in H]; try nia. rewrite H in *. 
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H4]; try (rewrite map_length; nia).
        clear -H1 H3. rewrite nth_error_map in H3. rewrite H1 in H3. ss. clarify.
      + assert (map_blk sk tge blk <> map_blk sk tge b).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
      + assert (map_blk sk tge blk <> map_blk sk tge b).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
    - exfalso. apply n. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. eapply r. rewrite map_length in H. nia.
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
          { left. instantiate (1:= map_blk src blk0). ii. apply map_blk_inj in H; eauto. }
          i. erewrite H. apply MMEM in H. des. eauto.
        * apply sumbool_to_bool_false in Heq0. hexploit Mem.load_store_other; eauto.
          2:{ i. erewrite H. apply MMEM in H. des. eauto. }
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
    - apply sumbool_to_bool_true in H. clarify; ss.
      unfold Values.Val.cmplu. ss. unfold Values.Val.of_bool. rewrite Int64.eq_true. ss.
    - apply sumbool_to_bool_false in H. clarify; ss.
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
    - bsimpl. des. apply sumbool_to_bool_true in H; clarify. apply sumbool_to_bool_true in H1; clarify; clarify.
      clear Heq. unfold Values.Val.cmplu. ss. des_ifs; bsimpl; des.
      all: try (rewrite Ptrofs.eq_true; ss).
      all: exfalso; eapply valid_ptr_contra; eauto.
    - bsimpl; des.
      + apply sumbool_to_bool_false in H. rename H into BLK. unfold Values.Val.cmplu. ss. des_ifs.
        1,2: apply map_blk_inj in e; clarify.
        bsimpl. des.
        { pose (valid_ptr_contra _ _ WFA Heq Heq2). clarify. }
        { pose (valid_ptr_contra _ _ WFB Heq0 Heq2). clarify. }
      + apply sumbool_to_bool_false in H. rename H into OFS. unfold Values.Val.cmplu. ss. des_ifs.
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
