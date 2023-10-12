Require Import Coqlib.
Require Import ITreelib.
Require Import ModSem.
Require Import Ordinal.Arithmetic.
Require Import STB.
Require Import HeapsortHeader.
Require Import HTactics ProofMode .
Require Import ClightProofs.
Require Import ConvC2ITree.
Require Import Clight_Mem1.
From compcertip Require Import Floats Integers Values Ctypes Memory Clightdefs. 

Lemma unfold_iter_eq:
  ∀ (E : Type → Type) (A B : Type) (f : A → itree E (A + B)) (x : A),
    ITree.iter f x = ` lr : A + B <- f x;; match lr with
                                          | inl l => tau;; ITree.iter f l
                                          | inr r => Ret r
                                          end.
Proof. intros. eapply bisim_is_eq. eapply unfold_iter. Qed. 
  
Notation "'cGet' i m" := (Maps.PTree.get i m) (at level 60, i at level 9, m at level 10).
Notation "'cSet' i v m" := (Maps.PTree.set i v m) (at level 60, i at level 9, v at level 9, m at level 10).

Lemma no_overflow_int64 (a : Z) : (0 <= a < Int64.modulus)%Z -> Int64.intval (Int64.repr a) = a.
Proof. rewrite Int64.unsigned_repr_eq. apply Z.mod_small. Qed.

Lemma no_overflow_int (a : Z) : (0 <= a < Int.modulus)%Z -> Int.intval (Int.repr a) = a.
Proof. rewrite Int.unsigned_repr_eq. apply Z.mod_small. Qed.

Lemma no_overflow_ptrofs (a : Z) : (0 <= a < Int64.modulus)%Z -> Ptrofs.intval (Ptrofs.repr a) = a.
Proof. rewrite Ptrofs.unsigned_repr_eq. apply Z.mod_small. Qed.

Lemma two_is_2 : Int.signed (Int.repr 2) = 2%Z.
Proof. rewrite Int.signed_repr_eq. auto. Qed.

Lemma one_is_1 : Int.signed (Int.repr 1) = 1%Z.
Proof. rewrite Int.signed_repr_eq. auto. Qed.

Ltac unfold_all :=
  unfold Ptrofs.mul, Ptrofs.divu, Ptrofs.sub, Ptrofs.add, Ptrofs.of_ints, Ptrofs.of_int64,
    Ptrofs.unsigned, Int64.mul, Int64.divu, Int64.sub, Int64.add, Int64.unsigned,
    Int.mul, Int.divu, Int.sub, Int.add, Int.unsigned in *.

Ltac resolve_loop := rewrite decomp_loop;unfold ConvC2ITree._sloop_itree;unfold sloop_iter_body;unfold sloop_iter_body_one;steps.
Ltac resolve_if := rewrite decomp_if; unfold _site_c;steps;unfold sem_binarith_c;unfold sem_cast_c;steps.
Ltac resolve_asgn := rewrite decomp_asgn; unfold _sassign_c; steps.
Ltac resolve_seq := repeat rewrite decomp_seq;steps.

Ltac use_get :=
  multimatch goal with
  | H : Maps.PTree.get _ _ = Some _ |- _ => rewrite H
  end.

Ltac resolve_var := repeat (repeat (rewrite Maps.PTree.gso;[|solve [auto]])
                            ;first [rewrite Maps.PTree.gss|rewrite Maps.PTree.gempty|use_get])
                    ;unfold sem_mul_c;unfold sem_div_c;unfold sem_binarith_c;unfold sem_cast_c;steps.

Ltac resolve_get :=
  multimatch goal with
  | H: Maps.PTree.get _ _ = Some _ |- _
    => repeat (rewrite Maps.PTree.gso in H;[|solve [auto]])
       ;rewrite Maps.PTree.gss in H
  end.

Ltac resolve_set := rewrite decomp_set;steps;repeat resolve_get;resolve_var;unfold_all;steps.

Ltac resolve_premem spec_incl depth :=
  unfold ccallU;steps;acatch;
  [eapply spec_incl;stb_tac;auto
  |instantiate (1 := depth);try apply OrdArith.lt_add_r;apply OrdArith.lt_from_nat;nia|].

Ltac resolve_load valid_array :=
  hcall (_, _, _, _) _ with valid_array;        
  [iModIntro;iSplit;ss;iSplit;ss;iSplit;ss
  |simpl;split;oauto;split;auto;let s := fresh "H" in intros s;discriminate s|];
  mDesAll;des;clarify;steps.

(* Ltac resolve_load MEMINCL load_point lemma depth  := *)
(*   unfold ccallU;steps;mApply points_to_token "A"; *)
(*   [|instantiate (1 := load_point);rewrite encode_list_len; *)
(*     rewrite map_length;unfold size_chunk_nat;simpl;nia]; *)
(*   mDesSep "A" as "PRE" "A";mDesAll;rewrite lemma in ACC; *)
(*   acatch;[eapply MEMINCL;stb_tac;auto *)
(*          |instantiate (1 := depth);try apply OrdArith.lt_add_r;apply OrdArith.lt_from_nat;nia|]; *)
(*   hcall (_, _, _, _) _ with "PRE"; *)
(*   [iModIntro;iSplit;ss;iSplit;[iSplit;try iPureIntro|iPureIntro];auto *)
(*   |simpl;split;oauto;split;auto;intros H0;discriminate H0|]; *)
(*   mDesAll;des;clarify;mSpcWand "A" with "POST";steps. *)

Ltac resolve_save valid_array :=
  hcall (_, _, _, _) _ with valid_array;        
  [iModIntro;iSplit;ss;iSplit;ss;iExists _;iSplit;ss;iSplit;ss
  |simpl;split;oauto;split;auto;let s := fresh "H" in intros s;discriminate s|];
  mDesAll;des;clarify;steps.

(* Ltac resolve_save MEMINCL save_point save_list lemma1 lemma2 depth := *)
(*   unfold ccallU;steps; *)
(*   mApply points_to_save "A"; *)
(*   [..|instantiate (1 := save_list); *)
(*    instantiate (1 := save_point);rewrite encode_list_len; *)
(*    rewrite map_length;rewrite lemma1;unfold size_chunk_nat; *)
(*    repeat (rewrite updblk_len); simpl];try nia; *)
(*   mDesSep "A" as "PRE" "A"; rewrite lemma2 in ACC; *)
(*   acatch; [eapply MEMINCL; stb_tac; auto| *)
(*             instantiate (1 := depth); apply OrdArith.lt_from_nat; nia|]; *)
(*   hcall (_, _, _ , _ ) _ with "PRE"; *)
(*   [iModIntro;do 2 (iSplit;ss); iExists _; *)
(*    iSplit;try iSplit;[ss| |iApply "PRE"]; *)
(*    rewrite lemma1; rewrite getblk_len;auto; *)
(*    rewrite encode_list_len; rewrite map_length; *)
(*    repeat (rewrite updblk_len;simpl;try nia); *)
(*    unfold size_chunk_nat; simpl; nia| *)
(*     simpl; split; oauto; split; auto; intros H0; discriminate H0|]; *)
(*   mDesAll; des;clarify; mSpcWand "A" with "POST";steps. *)

Ltac resolve_call str :=
   rewrite decomp_call; unfold _scall_c; prep;
   repeat (repeat (rewrite Maps.PTree.gso;[|solve [auto]])
           ;first [rewrite Maps.PTree.gss|rewrite Maps.PTree.gempty|use_get]);
   unfold Globalenvs.Genv.find_symbol;
   unfold Globalenvs.Genv.find_funct;
   unfold Globalenvs.Genv.find_funct_ptr;
   unfold Globalenvs.Genv.find_def; s;
   repeat (repeat (rewrite Maps.PTree.gso;[|solve [auto]])
           ;first [rewrite Maps.PTree.gss|use_get]); prep;
   replace (Globalenvs.Genv.invert_symbol _ _)
     with (Some (ident_of_string str)) by auto;
   unfold sem_cast_c;
   repeat (repeat (rewrite Maps.PTree.gso;[|solve [auto]])
           ;first [rewrite Maps.PTree.gss|use_get]);
   steps.