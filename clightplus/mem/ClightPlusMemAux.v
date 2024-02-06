Require Import CoqlibCCR.
From compcert Require Import AST Integers Values Memory Globalenvs.
From stdpp Require Import numbers.

Local Open Scope Z.

Lemma repeat_nth_some
  X (x: X) n ofs
  (IN: (ofs < n)%nat):
  <<NTH: nth_error (repeat x n) ofs = Some x>>.
Proof.
  ginduction n; ii; ss.
  - lia.
  - destruct ofs; ss. exploit IHn; et. lia.
Qed.

Lemma repeat_nth_none
  X (x: X) sz ofs
  (IN: ~(ofs < sz)%nat) :
  <<NTH: nth_error (repeat x sz) ofs = None>>.
Proof.
  generalize dependent ofs. induction sz; ii; ss.
  - destruct ofs; ss.
  - destruct ofs; ss. { lia. } hexploit (IHsz ofs); et. lia.
Qed.

Lemma repeat_nth
  X (x: X) sz ofs :
  nth_error (repeat x sz) ofs = if (ofs <? sz)%nat then Some x else None
.
Proof.
  des_ifs.
  - eapply repeat_nth_some; et. rewrite <- Nat.ltb_lt. et.
  - eapply repeat_nth_none; et. rewrite Nat.ltb_ge in Heq. lia.
Qed.

Local Transparent Mem.alloc.
Local Transparent Mem.store.

Local Ltac solve_len := unfold encode_int, bytes_of_int, rev_if_be, inj_bytes in *;
                        change Archi.big_endian with false in *;
                        change Archi.ptr64 with true in *; ss.

Lemma nth_error_ext A (l0 l1: list A) : (forall i, nth_error l0 i = nth_error l1 i) -> l0 = l1.
Proof.
  revert l1. induction l0; i; ss.
  - specialize (H 0%nat). ss. destruct l1; ss.
  - dup H. specialize (H 0%nat). ss. destruct l1; ss. clarify. f_equal.
    apply IHl0. i. specialize (H0 (S i)). ss.
Qed.

Lemma nth_error_getN n i m idx : 
  (idx < n)%nat ->
  nth_error (Mem.getN n i m) idx = Some (Maps.ZMap.get (i + (Z.of_nat idx)) m).
Proof.
  i. ginduction n; i; ss; try nia.
  destruct idx.
  - ss. rewrite Z.add_0_r. et.
  - ss. replace (i + S idx) with ((i + 1) + idx) by nia. apply IHn. nia.
Qed.

Lemma setN_inside x l i c entry
  (IN_RANGE: i ≤ x /\ (x < i + Z.of_nat (length l)))
  (ENTRY: nth_error l (Z.to_nat (x - i)) = Some entry)
:
  Maps.ZMap.get x (Mem.setN l i c) = entry.
Proof.
  assert (Z.to_nat (x - i)%Z < length l)%nat by nia.
  apply nth_error_Some in H. destruct (nth_error _ _) eqn: E in H; clarify.
  clear H. move l at top. revert_until l. induction l; i; ss; try nia.
  destruct (Nat.eq_dec (Z.to_nat (x - i)) 0).
  - rewrite e in *. ss. clarify. assert (x = i) by nia. rewrite H in *.
    rewrite Mem.setN_outside; try nia. apply Maps.ZMap.gss.
  - change (a :: l) with ([a] ++ l) in E. rewrite nth_error_app2 in E; ss; try nia.
    replace (Z.to_nat (x - i) - 1)%nat with (Z.to_nat (x - (i + 1))) in E by nia.
    eapply IHl; et. nia.
Qed.


Lemma alloc_store_zero_condition m m0 m1 start len b
  (ALLOC: Mem.alloc m start (start + len) = (m0, b))
  (STORE_ZEROS: Globalenvs.R_store_zeros m0 b start len (Some m1))
:
  <<FILLED_ZERO: forall ofs, start ≤ ofs < start + len ->
                  Maps.ZMap.get ofs (Maps.PMap.get b m1.(Mem.mem_contents)) = Byte Byte.zero>>.
Proof.
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
    rewrite H0. unfold Mem.store in e0. des_ifs. ss.
    rewrite Maps.PMap.gss. erewrite setN_inside; solve_len; try nia.
    replace (ofs - p) with 0 by nia. et.
  - hexploit IHSTORE_ZEROS; et. i. des. eapply H0. nia.
Qed.

Lemma match_mem_getN f (c d: Maps.ZMap.t memval) n p
    (MM: forall i mv, Maps.ZMap.get i c = mv -> Maps.ZMap.get i d = f mv)
  :
    Mem.getN n p d = map f (Mem.getN n p c).
Proof.
  revert p. induction n; i; ss.
  rewrite IHn. f_equal. erewrite <- MM; try reflexivity.
Qed.

Lemma proj_determines_decode_val l :
  proj_bytes l = None -> proj_fragment l = None -> decode_val Mptr l = Vundef.
Proof.
  i. unfold decode_val. des_ifs.
  destruct l; ss. destruct m; et.
  destruct proj_fragment eqn: X; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 5 (destruct n; clarify).
  destruct n; clarify.
  destruct n; clarify.
  destruct n; clarify.
  ss. destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 7 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 6 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 5 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 4 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 3 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 2 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  destruct n; clarify. ss.
  destruct l; clarify.
Qed.

Lemma pure_memval_good_decode l chunk mem :
    bytes_not_pure l = false -> chunk <> Many64 ->
    decode_val chunk (Mem.normalize_to_fragment chunk (Mem.decode_normalize chunk mem l)) = decode_val chunk l.
Proof.
  destruct chunk; clarify.
  i. rewrite Mem.decode_normalize_pure; et.
  unfold Mem.normalize_to_fragment.
  des_ifs.
  - unfold bytes_not_pure, proj_fragment_byte_mixed, proj_fragment_mixed in *.
    bsimpl. destruct l; ss. destruct m; clarify.
  - unfold decode_val. rewrite Heq0. des_ifs.
    unfold Val.load_result. rewrite proj_inj_value. et.
  - exfalso. clear - H Heq0 Heq1 Heq2. revert l0 H Heq0 Heq1 Heq2. induction l; ss.
    i. hexploit Mem.pure_tl_pure; et. unfold bytes_not_pure, proj_fragment_byte_mixed, proj_fragment_mixed in H.
    destruct a; ss.
    + destruct proj_bytes eqn:? in Heq0; clarify. des_ifs. bsimpl. destruct H.
      i. eapply IHl; et. destruct l; ss. clear -H. revert H. induction l; ss; clarify.
      { i. destruct m; ss. }
      i. destruct m; ss.
    + destruct proj_fragment eqn:? in Heq1; clarify. des_ifs. bsimpl. destruct H.
      i. eapply IHl; et. destruct l; ss. clear - H. revert H. induction l; ss; clarify.
      { i. destruct m; ss. }
      i. destruct m; ss.
Qed.

Lemma decode_encode_id_is_pure : forall chunk v, decode_val chunk (encode_val chunk v) = v -> bytes_not_pure (encode_val chunk v) = false.
Proof. i. unfold decode_val, encode_val in H. des_ifs. Qed.

Lemma concrete_store_zeros m1 b p n m2
        (STORE: store_zeros m1 b p n = Some m2):
  m1.(Mem.mem_concrete)= m2.(Mem.mem_concrete).
Proof.
  simpl in STORE. symmetry in STORE. apply Globalenvs.R_store_zeros_correct in STORE.
  remember (Some m2) as m'. revert m2 Heqm'.
  induction STORE; i.
  + clarify.
  + apply Mem.concrete_store in e0. rewrite e0.
    apply IHSTORE. assumption.
  + clarify.
Qed.