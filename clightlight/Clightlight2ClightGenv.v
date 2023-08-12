From compcert Require Import Maps Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
From ExtLib Require Import Data.List.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

Require Import ConvC2ITreeStmt.
Require Import Clightlight2ClightMatch.

From compcert Require Import Ctypes Clight Clightdefs.

Import Permutation.

Set Implicit Arguments.

Section GENV.

  Context `{Σ: GRA.t}.

  Variable types : list composite_definition.
  Variable defs : list (ident * globdef fundef type).
  Variable WF_TYPES : wf_composites types.
  Variable sge : alist string Any.t.
  Let ce := let (ce, _) := build_composite_env' types WF_TYPES in ce.

  Lemma found_itree_clight_function
        (fn: string) 
        (i: list Values.val -> itree Es Values.val) 
        (mn: string) (p: ident)
        (FOUND : find
                    ((fun '(k2, _) => fn ?[ eq ] k2) <*>
                     map_snd
                      (fun sem => transl_all mn (T:=Any.t) ∘ sem) <*>
                     (fun '(fn, f) => (string_of_ident fn, cfunU f)))
                    (decomp_fundefs types WF_TYPES sge defs) = 
                 Some (p, i))
    :
      (ident_of_string fn = p) /\ (In (p, i) (decomp_fundefs types WF_TYPES sge defs)).
  Proof.
    apply find_some in FOUND. des. split; auto.
    unfold compose in FOUND0. simpl in FOUND0. rewrite eq_rel_dec_correct in FOUND0. des_ifs.
  Admitted.

  Lemma decomp_fundefs_decomp_func i p
        (INLEFT: In (p, i) (decomp_fundefs types WF_TYPES sge defs)) 
    :
        exists f, 
          (i = fun vl => 
                v <- decomp_func sge ce f vl;; 
                (if Pos.eq_dec p (ident_of_string "main")
                 then (match v with Values.Vint _ => Ret v | _ => triggerUB end)
                 else Ret v)) /\ In (p, Gfun (Internal f)) defs.
  Proof.
    induction defs.
    { inv INLEFT. }
    destruct a as [? [[|]|]].
    2, 3: apply IHl in INLEFT; des; simpl; eauto.
    simpl in INLEFT. des.
    2: apply IHl in INLEFT; des; simpl; eauto.
    inv INLEFT. simpl. eexists; split; eauto.
  Qed.  
  
  Lemma in_def_gdefs a clight_prog
        (INDEFS_FUN: In a defs)
        (RIGHT_COMP: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
    :
        In a clight_prog.(prog_defs).
  Proof.
    unfold mkprogram, build_composite_env' in *. des_ifs.
  Qed.

  Lemma tgt_genv_match_symb_def
        clight_prog name b gd1 gd2
        (NO_REP: Coqlib.list_norepet (List.map fst defs))
        (RIGHT_COMP: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
        (GFSYM: Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string name) = Some b)
        (GFDEF: Genv.find_def (Genv.globalenv clight_prog) b = Some gd1)
        (INTGT: In (ident_of_string name, gd2) (prog_defs clight_prog))
    :
      gd1 = gd2.
  Proof.
    assert (AST.prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    assert (prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. rewrite H. auto. }
    { eauto. }
    i. apply Genv.find_def_symbol in H1. des. clarify.
  Qed.

  Lemma tgt_genv_find_def_by_blk
        clight_prog name b gd 
        (NO_REP: Coqlib.list_norepet (List.map fst defs))
        (RIGHT_COMP: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
        (GFSYM: Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string name) = Some b)
        (INTGT: In (ident_of_string name, gd) (prog_defs clight_prog))
    :
      Genv.find_def (Genv.globalenv clight_prog) b = Some gd.
  Proof.
    assert (AST.prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    assert (prog_defs clight_prog = defs) by now
      unfold mkprogram, build_composite_env' in *; des_ifs.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. rewrite H. auto. }
    { eauto. }
    i. apply Genv.find_def_symbol in H1. des. clarify.
  Qed.

End GENV.