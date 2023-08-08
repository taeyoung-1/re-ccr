From compcert Require Import Maps Clight Clightdefs.
From ExtLib Require Import Data.List.
Require Import Coqlib.
Require Import PCM.
Require Import AList.

Require Import Clightlight2ClightMatch.

Set Implicit Arguments.

Section LENV.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Lemma match_update_le defs le tle o v
        (MLE: match_le defs le tle)
    :
      match_le defs (set_opttemp o v le) (set_opttemp o (map_val defs v) tle).
  Proof.
    destruct o; ss. econs. i. inv MLE. destruct (Pos.eq_dec i id).
    - subst. rewrite PTree.gss in *. clarify.
    - rewrite PTree.gso in *; et.
  Qed.

  Lemma update_le
        defs x id v sv le tle
        (SRC_UPDATE: Maps.PTree.get x (Maps.PTree.set id v tle) = Some sv)
        (MLE: match_le defs le tle)
    :
      Maps.PTree.get x (Maps.PTree.set id (map_val defs v) tle) = Some (map_val defs sv).
  Proof.
  Admitted.

  Lemma bind_parameter_temps_exists_if_same_length
        params args tle0
        (LEN: List.length params = List.length args)
    :
      exists tle, (<<BIND: bind_parameter_temps params args tle0 = Some tle>>).
  Proof.
    depgen args. depgen tle0. clear. induction params; i; ss; clarify.
    { exists tle0. des_ifs. }
    destruct args; ss; clarify. destruct a. eauto.
  Qed.

  Lemma bind_parameter_temps_exists
        defs base params sle rvs (tle0: temp_env)
        (BIND_SRC: bind_parameter_temps params rvs base = Some sle)
    :
      exists tle, (<<BIND_TGT: bind_parameter_temps params (List.map (map_val defs) rvs) tle0
                      = Some tle>>).
  Proof.
    eapply bind_parameter_temps_exists_if_same_length; eauto.
    rewrite ! map_length. clear -BIND_SRC. depgen base. revert sle.  depgen rvs. depgen params.
    induction params; i; ss; des_ifs.
    ss. f_equal. eapply IHparams; eauto.
  Qed.

(*   Lemma init_lenv_match
        src le tle l
        (SINIT: le = init_lenv l)
        (TINIT: tle = create_undef_temps (List.map s2p l))
    :
      <<MLINIT: match_le src le tle >>.
  Proof.
    red. depgen src. depgen le. depgen tle. clear. induction l; ii; ss; clarify.
    match goal with
    | [ |- match_le _ (_ :: ?_le0) (PTree.set _ _ ?_tle0)] => specialize IHl with (tle:=_tle0) (le:=_le0) (src:=src) end.
    hexploit IHl; eauto. clear IHl. i. inv H.
    econs. i. ss. des_ifs.
    { rewrite eq_rel_dec_correct in Heq. des_ifs. rewrite PTree.gss. ss. }
    apply neg_rel_dec_correct in Heq.
    rewrite PTree.gso; eauto. ii. apply Heq. apply s2p_inj in H0. ss.
  Qed. *)

  (*** TODO: lenv initialization has match ***)
(*   Lemma _initial_lenv_match
        src params rvs le0 le (tle0: temp_env) tle
        (ML0: match_le src le0 tle0)
        (ARGS: init_args params rvs le0 = Some le)
        (BIND: bind_parameters (List.map s2p params)
                               (List.map (map_val src) rvs) tle0
               = Some tle)
    :
      (<<MLINIT: match_le src le tle>>).
  Proof.
    red. move params before builtins. revert_until params. clear. induction params; i; ss; clarify.
    { destruct rvs; ss; clarify. }
    destruct rvs eqn:RVS; ss; clarify.
    eapply IHparams.
    2: eapply ARGS.
    2: eapply BIND.
    depgen ML0. clear; i. econs; i. eapply alist_update_le; eauto.
  Qed.

  Lemma initial_lenv_match
        src impf rvs le0 le (tle0: temp_env)
        (SINIT: le0 = init_lenv (impf.(Imp.fn_vars) ++ ["return"; "_"]))
        (ARGS: init_args impf.(Imp.fn_params) rvs le0 = Some le)
        (TINIT: tle0 = create_undef_temps
                         (List.map (fun vn : string => s2p vn) (impf.(Imp.fn_vars) ++ ["return"; "_"])))
    :
      exists tle, (<<BIND: bind_parameters
                        (List.map (fun vn : string => s2p vn) impf.(Imp.fn_params))
                        (List.map (map_val src) rvs) tle0 = Some tle>>) /\
             (<<MLINIT: match_le src le tle>>).
  Proof.
    hexploit bind_parameters_exists; eauto. i. des.
    exists tle. split; eauto.
    eapply _initial_lenv_match; eauto.
    eapply init_lenv_match; eauto.
  Qed. *)

End LENV.
