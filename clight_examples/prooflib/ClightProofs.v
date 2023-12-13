Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HTactics ProofMode.
Require Import SimModSem.
Require Import Coq.Sorting.Sorted.
From compcert Require Import Floats Integers Values Ctypes Memory.
Require Import ConvC2ITree.
Require Import Clight_Mem0.
Require Import Clight_Mem1.
Require Import List.
Import ListNotations.
Set Implicit Arguments.

Section POINTS_TO.
  Definition updblk A i f l l' : list A := firstn i l ++ l' ++ skipn f l.
  Definition getblk A i ofs l : list A := firstn ofs (skipn i l).

  Lemma getblk_len A (i ofs : nat) (l : list A) : i + ofs <= length l -> length (getblk i ofs l) = ofs.
  Proof.
    intros. unfold getblk. rewrite take_length_le;auto.
    rewrite drop_length. nia.
  Qed.
  
  Lemma updblk_len A (i f : nat) (l : list A) (l' : list A) :
    (i <= f)%nat
    -> length l' = (Nat.min (length l) f - i)%nat
    -> length (updblk i f l l') = length l.
  Proof.
    intros. unfold updblk. do 2 rewrite app_length.
    rewrite H0. rewrite take_length. rewrite drop_length. nia.
  Qed.

  Lemma decode_int : forall def chunk m l,
      (m < length l)%nat
      -> decode_val chunk (getblk (m * (size_chunk_nat chunk)) (size_chunk_nat chunk) (encode_list chunk (map Vint l)))
         = decode_val chunk (encode_val chunk (Vint (nth m l def))).
  Proof.
    Opaque encode_val.
    intros def chunk m l0. revert chunk m def. induction l0;intros;simpl.
    - simpl in H. nia. 
    - unfold getblk. destruct m.
      + simpl. unfold drop. erewrite <- encode_val_length. rewrite take_app. auto.
      + simpl in *. erewrite <- encode_val_length. rewrite drop_plus_app;eauto. 
        erewrite <- IHl0;try nia. unfold getblk. 
        erewrite <- encode_val_length. auto.
        Transparent encode_val.
  Qed.

  Lemma upd_encode_comm : forall chunk i f l l',
      encode_list chunk (map Vint (updblk i f l l'))
                         = updblk (i * (size_chunk_nat chunk)) (f * (size_chunk_nat chunk)) (encode_list chunk (map Vint l)) (encode_list chunk (map Vint l')).
  Proof.
    Opaque encode_val.
    intros chunk i f l l'. symmetry. revert chunk i f l'. induction l;intros;simpl.
    - unfold updblk. simpl. destruct i;simpl.
      + destruct f;simpl.
        * do 2 rewrite app_nil_r. auto.
        * rewrite app_nil_r. 
          destruct (size_chunk_nat chunk + f * size_chunk_nat chunk)%nat eqn : E.
          ** simpl. rewrite app_nil_r. auto.
          ** simpl. rewrite app_nil_r. auto.
      + destruct f;simpl.
        * do 2 rewrite app_nil_r.
          destruct (size_chunk_nat chunk + i * size_chunk_nat chunk)%nat;auto.
        * rewrite app_nil_r.
          destruct (size_chunk_nat chunk + i * size_chunk_nat chunk)%nat;
            destruct (size_chunk_nat chunk + f * size_chunk_nat chunk)%nat;
            rewrite app_nil_r;auto.
    - unfold updblk.
      destruct f;destruct i.
      + simpl. unfold drop. rewrite map_app. simpl. unfold encode_list. rewrite flat_map_app.
        simpl. auto.
      + simpl. rewrite take_plus_app;try apply encode_val_length. rewrite <- app_assoc. unfold drop.
        rewrite app_inv_head_iff.
        replace (l' ++ a :: l) with ((l'++[a]) ++ drop 0 l).
        2 :{ unfold drop. rewrite <- app_assoc. simpl. auto. }
        replace (take i l ++ (l' ++ [a]) ++ drop 0 l) with (updblk i 0 l (l' ++ [a]))
          by now unfold updblk;auto.
        rewrite <- IHl. unfold updblk. rewrite map_app. simpl.
        unfold encode_list. rewrite flat_map_app. simpl. rewrite <- app_assoc. unfold drop.
        rewrite app_nil_r. auto.
      + simpl. rewrite drop_plus_app;try apply encode_val_length.
        replace (l' ++ drop f l) with (updblk 0 f l l') by now unfold updblk;simpl;auto.
        rewrite <- IHl. unfold updblk. simpl. auto.
      + simpl. rewrite take_plus_app;try apply encode_val_length.
        rewrite drop_plus_app;try apply encode_val_length. unfold updblk in IHl. rewrite <- IHl.
        rewrite <- app_assoc. auto.
  Qed.
  Lemma drop_encode_comm : forall chunk n l,
      encode_list chunk (map Vint (drop n l)) = drop (n * (size_chunk_nat chunk)) (encode_list chunk (map Vint l)).
  Proof.
    i. revert n chunk. induction l;i;ss.
    - do 2 rewrite drop_nil. ss.
    - destruct n;ss.
      rewrite IHl. rewrite drop_plus_app;try apply encode_val_length. auto.
  Qed.

  Lemma take_encode_comm : forall chunk n l,
      encode_list chunk (map Vint (take n l)) = take (n * (size_chunk_nat chunk)) (encode_list chunk (map Vint l)).
  Proof.
    i. revert n chunk. induction l;i;ss.
    - do 2 rewrite take_nil. ss.
    - destruct n;ss.
      rewrite IHl. rewrite take_plus_app;try apply encode_val_length. auto.
  Qed.
  
  Lemma get_encode_comm : forall chunk i f l,
    encode_list chunk (map Vint (getblk i f l)) =
      getblk (i * (size_chunk_nat chunk)) (f * (size_chunk_nat chunk)) (encode_list chunk (map Vint l)).
  Proof.
    unfold getblk. i. rewrite take_encode_comm. rewrite drop_encode_comm. auto.
  Qed.
 
  Lemma encode_list_len chunk l: length (encode_list chunk l) = ((size_chunk_nat chunk) * length l)%nat.
  Proof.
    induction l;simpl;auto.
    rewrite app_length. rewrite IHl. rewrite <- (encode_val_length _ a). nia.
  Qed.

  Let _memRA: URA.t := (block ==> Z ==> (Excl.t memval))%ra.
  Instance memRA: URA.t := Auth.t _memRA.

  Context `{@GRA.inG memRA Σ}.
  Local Arguments Z.of_nat: simpl nomatch.

  Section SEP.
  Lemma _points_to_app l l' blk ofs:
    (_points_to (blk, ofs) (l++l')) = (_points_to (blk, ofs) l) ⋅ (_points_to (blk, ofs + length l) l').
  Proof.
    revert l' blk ofs. induction l;i;ss.
    - rewrite points_to_nil. rewrite URA.unit_idl. rewrite Z.add_0_r. auto.
    - rewrite points_to_split. rewrite (points_to_split blk ofs a l).
      replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l)))
        with ((ofs + 1) + length l) by nia.
      rewrite <- URA.add_assoc. rewrite <- IHl. auto.
  Qed.

  Lemma _points_to_split :
    forall (blk : Values.block) (ofs : Z) (n : nat) (l : list memval),
      _points_to (blk, ofs) l =
        _points_to (blk, ofs) (firstn n l) ⋅ _points_to (blk, ofs + (length (firstn n l))) (skipn n l).
  Proof.
    intros. set l as k at 2 3 4. rewrite <- (firstn_skipn n l). unfold k. clear k.
    rewrite _points_to_app. auto.
  Qed.

  Lemma _points_to_split':
    forall (blk : Values.block) (ofs : Z) (n : nat) (l : list memval),
      n <= (length l) ->
      _points_to (blk, ofs) l = _points_to (blk, ofs) (firstn n l) ⋅ _points_to (blk, ofs + n) (skipn n l).
  Proof.
    intros. rewrite (_points_to_split _ _ n). rewrite firstn_length_le;[auto|nia].
  Qed.

  Lemma _points_to_token :
    forall blk ofs (n : nat) (m : Z) l,
      0 <= m <= length l ->
      (blk, ofs) |-> l -∗
       ((blk, (ofs + m)%Z) |-> getblk (Z.to_nat m) n l **
           (((blk, (ofs + m)%Z) |-> getblk (Z.to_nat m) n l ) -* ((blk, ofs) |-> l))).
  Proof.
    intros. iIntros "A". unfold getblk, points_to. destruct H0 as [S1 S2].
    assert (S3 : Z.to_nat m ≤ strings.length l) by nia.
    pose proof (_points_to_split' blk ofs (Z.to_nat m) l S3) as Hr. set l as k at 4.
    rewrite Hr. unfold k. clear k.
    pose proof (_points_to_split blk (ofs + m) n (drop (Z.to_nat m) l)) as Ht.
    replace (ofs + Z.to_nat m) with (ofs + m) by nia.
    rewrite Ht. iDestruct "A" as "[A [B C]]".
    iSplitL "B";auto. iIntros "B". iCombine "B C" as "B". rewrite <- _points_to_split.
    iCombine "A B" as "A". replace (ofs + m) with (ofs + Z.to_nat m) by nia.
    rewrite <- _points_to_split';auto.
  Qed.

  Lemma _points_to_save :
    forall blk ofs (m : Z) l l',
      0 <= m ->
      m + (length l') <= length l ->
       ((blk, ofs) |-> l) -∗
        ( ((blk, (ofs + m)%Z) |-> getblk (Z.to_nat m) (length l') l) **
           (((blk, (ofs + m)%Z) |-> l' ) -* ((blk, ofs) |-> updblk (Z.to_nat m) (Z.to_nat m + length l') l l'))).
  Proof.
    intros. iIntros "A". unfold getblk, updblk, points_to.
    assert (Hi1 : (Z.to_nat m) ≤ strings.length l) by nia.
    pose proof (_points_to_split' blk ofs _ _ Hi1) as Hr. rewrite Hr.
    assert (Hi2 : length l' ≤ strings.length (drop (Z.to_nat m) l)) by now rewrite skipn_length;nia.
    pose proof (_points_to_split' blk (ofs + m) (length l') (drop (Z.to_nat m) l) Hi2) as Ht.
    replace (ofs + Z.to_nat m) with (ofs + m) by nia.
    rewrite Ht. iDestruct "A" as "[A [B C]]".
    iSplitL "B";auto. iIntros "B". rewrite _points_to_app. rewrite _points_to_app.
    iCombine "B C" as "B".  iCombine "A B" as "A". rewrite drop_drop.
    rewrite firstn_length_le;try nia.
    replace (ofs + Z.to_nat m) with (ofs + m) by nia. auto.
  Qed.  
End SEP.    
End POINTS_TO.

Section UNFOLD_DECOMP.
  Variable eff : Type -> Type.
  Context `{HasCall : callE -< eff}.
  Context `{HasEvent : eventE -< eff}.
  Variable ge : Clight.genv.
  Lemma decomp_seq
    (retty : type) (e : Clight.env) (le : Clight.temp_env) (s1 s2 : Clight.statement)
    : decomp_stmt ge retty (Clight.Ssequence s1 s2) e le
      = ` x_ : Clight.env * Clight.temp_env * option bool * option val <-
        decomp_stmt ge retty s1 e le;;
        (let (y, v) := x_ in
         let (y0, bc) := y in
         let (e', le') := y0 in
         match v with
         | Some _ => Ret (e', le', None, v)
         | None =>
             match bc with
             | Some _ => Ret (e', le', bc, None)
             | None => decomp_stmt ge retty s2 e' le'
             end
         end).
  Proof. auto. Qed.

  Lemma decomp_if (retty : type) (e : Clight.env) (le : Clight.temp_env) (a : Clight.expr) (s1 s2 : Clight.statement)
    : decomp_stmt ge retty (Clight.Sifthenelse a s1 s2) e le =
        ` b : option bool <- _site_c ge e le a;;
        match b with
        | Some true => decomp_stmt ge retty s1 e le
        | Some false => decomp_stmt ge retty s2 e le
        | None => triggerUB
        end.
  Proof. auto. Qed.
  
  Lemma decomp_set (retty : type) (e : Clight.env) (le : Clight.temp_env) (id : AST.ident) (a : Clight.expr)
    : decomp_stmt ge retty (Clight.Sset id a) e le =
        ` v : option val <- eval_expr_c ge e le a;;
        match v with
        | Some v0 => let le' := Maps.PTree.set id v0 le in Ret (e, le', None, None)
        | None => triggerUB
        end.
  Proof. auto. Qed.

  Lemma decomp_asgn (retty : type) (e : Clight.env) (le : Clight.temp_env) (a1 a2 : Clight.expr)
    : decomp_stmt ge retty (Clight.Sassign a1 a2) e le
      = (_ <- _sassign_c ge e le a1 a2 ;; Ret (e, le, None, None)).
  Proof. auto. Qed.

  Lemma decomp_skip (retty : type) (e : Clight.env) (le : Clight.temp_env)
    : decomp_stmt ge retty Clight.Sskip e le
      = Ret (e, le, None, None).
  Proof. auto. Qed.

  Lemma decomp_call (retty : type) (e : Clight.env) (le : Clight.temp_env) (optid : option AST.ident) (a : Clight.expr) (al : list Clight.expr)
    : decomp_stmt ge retty (Clight.Scall optid a al) e le
      = ` v : val <- _scall_c ge e le a al;; Ret (e, Clight.set_opttemp optid v le, None, None).
  Proof. auto. Qed.

  Lemma decomp_loop (retty : type) (e : Clight.env) (le : Clight.temp_env) (s1 s2 : Clight.statement)
    : decomp_stmt ge retty (Clight.Sloop s1 s2) e le
      = let itr1 := decomp_stmt ge retty s1 in
        let itr2 := decomp_stmt ge retty s2 in _sloop_itree e le itr1 itr2.
  Proof. auto. Qed.

  Lemma decomp_break (retty : type) (e : Clight.env) (le : Clight.temp_env)
    : decomp_stmt ge retty Clight.Sbreak e le
      = Ret (e, le, Some true, None).
  Proof. auto. Qed.

  Lemma decomp_conti (retty : type) (e : Clight.env) (le : Clight.temp_env) (s1 s2 : Clight.statement)
    : decomp_stmt ge retty Clight.Scontinue e le = Ret (e, le, Some false, None).
  Proof. auto. Qed.

  Lemma decomp_ret (retty : type) (e : Clight.env) (le : Clight.temp_env) (oa : option Clight.expr)
    : decomp_stmt ge retty (Clight.Sreturn oa) e le
      = ` v : option val <- _sreturn_c ge retty e le oa;;
        match v with
        | Some v0 => Ret (e, le, None, Some v0)
        | None => triggerUB
    end.
  Proof. auto. Qed.

  Lemma decomp_builtin (retty : type) (e : Clight.env) (le : Clight.temp_env) (optid : option AST.ident) (ef : AST.external_function) (targs : Ctypes.typelist) (el : list Clight.expr)
    : decomp_stmt ge retty (Clight.Sbuiltin optid ef targs el) e le
      = ` vargs : option (list val) <- eval_exprlist_c ge e le el targs;;                       ` vargs0 : list val <- unwrapU vargs;;
        match optid with
        | Some _ =>
            match ef with
            | AST.EF_capture =>
                match vargs0 with
                | [] => triggerUB
                | [v1] =>
                    match v1 with
                    | Vptr b ofs =>
                        z <- ccallU "capture" (b, ofs);;
                        Ret (e, (Clight.set_opttemp optid (Vptrofs z) le), None, None)
                    | Vlong i => 
                        if Archi.ptr64
                        then Ret (e, (Clight.set_opttemp optid (Vlong i) le), None, None)
                        else triggerUB
                    | Vint i => 
                        if Archi.ptr64
                        then triggerUB
                        else Ret (e, (Clight.set_opttemp optid (Vint i) le), None, None)
                    | _ => triggerUB
                    end
                | v1 :: _ :: _ => triggerUB
                end
            | _ => triggerUB
            end
        | None => triggerUB
        end.
  Proof. auto. Qed.
  
End DECOMP.
