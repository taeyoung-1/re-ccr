From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import IRed.
Require Import ClightPlusExprgen.
Require Import ClightPlusgen.
Require Import STS2SmallStep.
Require Import ClightPlusMem0.

Require Import ClightPlus2ClightMatchEnv.
Require Import ClightPlus2ClightMatchStmt.
Require Import ClightPlus2ClightArith.
Require Import ClightPlus2ClightLenv.
Require Import ClightPlus2ClightMem.
Require Import ClightPlus2ClightSimExpr.
Require Import ClightPlus2ClightSimStmt.

From compcert Require Import Values Ctypes Clight Clightdefs.

Section PROOF.

  Ltac rewriter :=
    try match goal with
        | H: _ = _ |- _ => rewrite H in *
        end; clarify.

  Ltac inv_pred P :=
    repeat match goal with
            | H: context G [P] |- _ =>
              lazymatch context G [P] with
              | forall _, _  => fail
              | _ => inv H
              end
            end; repeat rewriter.

  Ltac inv_pred_safe P :=
    solve [match goal with
            | H: context G [P] |- _ =>
              lazymatch context G [P] with
              | forall _, _  => fail
              | _ => inv H
              end
            end; repeat rewriter].

  Ltac determ LEMMA P :=
    repeat match goal with
            | H: context G [P] |- _ =>
              lazymatch context G [P] with
              | forall _, _  => fail
              | _ => revert H
              end
            end;
    let X1 := fresh "X" in
    let X2 := fresh "X" in
    intros X1 X2;
    hexploit LEMMA; [eapply X1|eapply X2|]; i; des; repeat rewriter.

  Section DETERM.

  Lemma Clight_eval_determ a ge e le m
    :
      (forall v0 v1
              (EXPR0: eval_expr ge e le m a v0)
              (EXPR1: eval_expr ge e le m a v1),
        v0 = v1) /\
      (forall vp0 vp1
              (EXPR0: eval_lvalue ge e le m a vp0)
              (EXPR1: eval_lvalue ge e le m a vp1),
        vp0 = vp1).
  Proof.
    revert_until a.
    induction a; split; i;
      inv EXPR0; try inv_pred_safe eval_expr; try inv_pred_safe eval_lvalue;
        inv EXPR1; try inv_pred_safe eval_expr; try inv_pred_safe eval_lvalue;
          try split; rewriter; et; repeat spc IHa; des; try determ IHa eval_expr.
    { inv_pred eval_lvalue; inv_pred deref_loc. }
    { inv_pred eval_lvalue; determ IHa eval_expr; inv_pred deref_loc. }
    { determ IHa0 eval_lvalue. }
    { repeat spc IHa1. repeat spc IHa2. des. exploit (IHa1 v2 v4); et. i. subst.
      exploit (IHa2 v3 v5); et. i. subst. rewriter. }
    { inv_pred eval_lvalue; determ IHa eval_expr; inv_pred deref_loc. }
  Qed.

  Lemma Clight_eval_expr_determ a ge e le m
    :
      forall v0 v1
              (EXPR0: eval_expr ge e le m a v0)
              (EXPR1: eval_expr ge e le m a v1),
        v0 = v1.
  Proof. edestruct Clight_eval_determ; et. Qed.

  Lemma Clight_eval_lvalue_determ a ge e le m
    :
      forall vp0 vp1
              (EXPR0: eval_lvalue ge e le m a vp0)
              (EXPR1: eval_lvalue ge e le m a vp1),
        vp0 = vp1.
  Proof. edestruct Clight_eval_determ; et. Qed.

  Lemma Clight_eval_exprlist_determ a
    :
      forall v0 v1 ge e le m ty
              (EXPR0: eval_exprlist ge e le m a ty v0)
              (EXPR1: eval_exprlist ge e le m a ty v1),
        v0 = v1.
  Proof.
    induction a; ss.
    { i. inv EXPR0. inv EXPR1. auto. }
    { i. inv EXPR0. inv EXPR1.
      determ Clight_eval_expr_determ eval_expr.
      determ IHa eval_exprlist. }
  Qed.

  Lemma alloc_variables_determ vars
    :
      forall e0 e1 ge ee m m0 m1
              (ALLOC0: alloc_variables ge ee m vars e0 m0)
              (ALLOC1: alloc_variables ge ee m vars e1 m1),
        e0 = e1 /\ m0 = m1.
  Proof.
    induction vars; et.
    { i. inv ALLOC0; inv ALLOC1; auto. }
    { i. inv ALLOC0; inv ALLOC1; auto. rewriter.
      eapply IHvars; et. }
  Qed.

  Lemma Clight_wf_semantics prog
    :
      wf_semantics (Clight.semantics2 prog).
  Proof.
    econs.
    { i. inv FINAL. inv STEP. }
    { i. inv FINAL0. inv FINAL1. ss. }
  Qed.

  End DETERM.

  Import ModSemL.

  Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Clight.program) => @sim_mon (ModL.compile src) (Clight.semantics2 tgt)).
  Hint Resolve _sim_mon: paco.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (step_tau _).

  Let arrow (A B: Prop): Prop := A -> B.
  Opaque arrow.

  Let oeq [A] (a: A) b: Prop := (a = b).
  Opaque oeq. 

  Ltac to_oeq :=
    match goal with
    | |- ?A = ?B => change (oeq A B)
    end.

  Ltac from_oeq :=
    match goal with
    | |- oeq ?A ?B => change (A = B)
    end.

  Ltac sim_redE :=
    to_oeq; cbn; repeat (Red.prw ltac:(_red_gen) 1 0); repeat (Red.prw ltac:(_red_gen) 2 0); from_oeq.

  Ltac to_arrow :=
    match goal with
    | |- ?A -> ?B => change (arrow A B)
    end.

  Ltac from_arrow :=
    match goal with
    | |- arrow ?A ?B => change (A -> B)
    end.
  Ltac sim_redH H :=
    revert H; to_arrow; (repeat (cbn; Red.prw ltac:(_red_gen) 2 2 0)); from_arrow; intros H.

  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := 
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac tgt_step := try pfold; econs 4; eexists; eexists.

  Ltac wrap_up := try pfold; econs 7; et; right.

  Ltac remove_UBcase := des_ifs; try sim_red; try sim_triggerUB.

  (* Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss. *)

  Ltac eapplyf NEXT := let X := fresh "X" in hexploit NEXT;[..|intro X; punfold X; eapply X].

  Ltac eapplyfarg NEXT modl ge := eapplyf NEXT; et; [instantiate (1:=modl)|instantiate (1:=ge)|..]; et. 

  Local Opaque Pos.of_nat.
  Local Opaque Pos.of_succ_nat.

  Lemma unfold_itree_iter A B eff (f : A -> itree eff (A + B)) (x: A)  :
          ITree.iter f x = `lr : A + B <- f x;;
                           match lr with
                            | inl l => tau;; ITree.iter f l
                            | inr r => Ret r
                           end.
  Proof.
    eapply bisim_is_eq. apply unfold_iter.
  Qed.

  Lemma call_cont_is_call_cont tcont : is_call_cont (call_cont tcont).
  Proof. induction tcont; et; ss. Qed.


  Lemma number_same_stmt eff CAL EV sk ce p p' retty stmt : @decomp_stmt eff CAL EV sk ce p retty stmt = @decomp_stmt eff CAL EV sk ce p' retty stmt.
  Proof.
    revert p p' retty. induction stmt; ss.
    - i. unfold hide. extensionalities. sim_redE. do 2 f_equal. erewrite IHstmt1.
      eapply bind_extk. i. des_ifs_safe. erewrite IHstmt2. et. 
    - i. unfold hide. extensionalities. sim_redE. do 2 f_equal. sim_redE.
      erewrite IHstmt1. erewrite IHstmt2. et.
    - i. unfold hide. unfold _sloop_itree. unfold hide.
      erewrite IHstmt1. erewrite IHstmt2. et.
  Qed.

  Lemma number_same_sloop eff EV'' CAL' CAL EV' EV p p' sk ce e le retty s1 s2 : @_sloop_itree eff EV'' p e le (fun p => @decomp_stmt eff CAL EV sk ce p retty s1) (fun p => @decomp_stmt eff CAL' EV' sk ce p retty s2) = @_sloop_itree eff EV'' p' e le (fun p => @decomp_stmt eff CAL EV sk ce p retty s1) (fun p => @decomp_stmt eff CAL' EV' sk ce p retty s2).
  Proof.
    unfold _sloop_itree. unfold hide. ss. f_equal. f_equal. f_equal.
    - erewrite number_same_stmt; et.
    - erewrite number_same_stmt; et. 
  Qed.

  Local Opaque ccallU.
  Local Opaque build_composite_env'.
  Local Opaque build_composite_env.

  Local Arguments ClightPlusgen._sassign_c /.
  Local Arguments ClightPlusgen._scall_c /.
  Local Arguments ClightPlusgen._site_c /.

  Local Arguments Es_to_eventE /.
  Local Arguments itree_of_stmt /. 
  Local Arguments sloop_iter_body_two /.
  Local Arguments ktree_of_cont_itree /.

  Lemma return_cont M pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    itr_cont v
    r b tstate tcont ty mn ms ce
    (MCONT: match_cont sk tge ce ms ty mn itr_cont tcont)
    (NEXT: forall itr_cont'' itr_cont',
            match_cont sk tge ce ms ty mn itr_cont' (call_cont tcont) ->
            itr_cont'' = 
              (`r0: (p_state * val) <- itr_cont' (pstate, (e, le, None, Some v));;
                let (_, retv) := r0 in Ret retv↑) ->
            paco4
              (_sim (ModL.compile M) (semantics2 cprog)) r true b
              itr_cont''
              tstate)
  :
    paco4
      (_sim (ModL.compile M) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- itr_cont (pstate, (e, le, None, Some v));;
        let (_, retv) := r0 in Ret retv↑)
      tstate.
  Proof.
    depgen v. induction MCONT; i.
    - rewrite ITR. ss. sim_red. eapply IHMCONT; et.
    - rewrite ITR. ss. sim_red. eapply IHMCONT; et.
    - rewrite ITR. ss. sim_red. eapply IHMCONT; et.
    - ss. eapply NEXT; et. econs; et. 
    - rewrite ITR. ss. sim_red. eapply NEXT. { econs; et. }
      sim_redE. et.
  Qed.

  Theorem match_states_sim
          sk ce
          (M modl internal_modl: ModL.t) ms
          (clight_prog : program) ist cst
          (MODL: modl = ModL.add (Mod.lift Mem) internal_modl)
          (INTERNAL: forall s fd, In (s, Gfun fd) internal_modl.(ModL.sk) -> exists f : Clight.function, fd = Internal f)
          (MODSEML: ms = modl.(ModL.enclose))
          (SK: sk = Sk.canon modl.(ModL.sk))
          (MS: match_states sk (Genv.globalenv clight_prog) ce (Ctypes.prog_comp_env clight_prog) ms ist cst)
  :
      <<SIM: sim (ModL.compile M) (Clight.semantics2 clight_prog) false false ist cst>>.
  Proof.
    red. red.
    depgen ist. depgen cst. pcofix CIH. i.
    inv MS. des_ifs_safe.
    set (Genv.globalenv _) as tge in *.
    set (Ctypes.prog_comp_env _) as tce in *.
    set (Sk.canon (ModL.sk (ModL.add Mem internal_modl))) as sk in *.
    set (ModL.add _ _) as modl in *.
    set {| genv_genv := tge; genv_cenv := tce |} as ge.
    assert (GCEQ: globalenv clight_prog = ge) by ss.
    destruct tcode.
    - ss. unfold hide. ss. sim_red.
      destruct tcont; inv MCONT; ss; clarify.
      + sim_red. sim_tau. sim_red. eapplyfarg step_freeing_stack internal_modl ge.
        i. sim_red. sim_triggerUB. 
      + sim_red. pfold. econs 4.
        { i. inv H; et. }
        { eexists. econs. } i.
        inv STEP; ss. sim_tau. 
        econs 8; et. right. apply CIH. econs; et.
      + sim_red. pfold. econs 4.
        { i. inv H; et. }
        { eexists. econs. et. } i.
        inv STEP; ss. sim_tau. 
        econs 8; et. right. apply CIH. econs; et. 
        { econs; et. }
        sim_redE. apply bind_extk. i. des_ifs_safe.
        repeat (des_ifs; sim_redE; try reflexivity).
      + sim_red. pfold. econs 4.
        { i. inv H; et. }
        { eexists. econs. } i.
        inv STEP; ss. sim_tau. 
        sim_red. sim_tau.
        econs 8; et. right. apply CIH.
        econs; et. erewrite number_same_sloop; et.
      + sim_red. sim_tau. sim_red. eapplyfarg step_freeing_stack internal_modl ge.
        i. sim_red. pfold. econs 4.
        { i. inv H1; et. }
        { eexists. econs; et. ss. } i.
        inv STEP; ss. sim_tau. 
        econs 4.
        { i. inv H1; et. }
        { eexists. econs; et. } i.
        inv STEP; ss.
        econs 8;[|des_ifs|];et. right. eapply CIH.
        rewrite GCEQ in H8. clarify.
        clear PSTATE. econs; et.
        { hexploit match_update_le; et. instantiate (2 := Vundef). ss. et. }
        { instantiate (1 := update pstate "Mem" (Any.upcast m')). ss. }
        ss. unfold hide. sim_redE. et.
    Local Opaque sem_cast_c.
    - ss. unfold hide. sim_red. sim_tau. sim_red.
      eapplyfarg step_eval_lvalue internal_modl ge. i. subst. sim_red.
      eapply step_eval_expr with (ge := ge) (modl:=internal_modl); et. i. subst. sim_red.
      eapply step_sem_cast with (modl:=internal_modl); et. i.
      unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
      eapply step_assign_loc with (modl:=internal_modl); et. i. sim_red.
      pfold. econs 4.
      { i. inv H4; et. }
      { eexists. econs; et. } i.
      inv STEP; des; clarify. ss.
      econs 8; et. right. eapply CIH. clear PSTATE.
      assert (m'0 = tm').
      { determ Clight_eval_lvalue_determ eval_lvalue.
        determ Clight_eval_expr_determ eval_expr.
        unfold tce in *. inv_pred assign_loc; des; clarify. }
      subst.
      econs; et.
      { instantiate (1 := update pstate "Mem" m'↑). unfold update. ss. } 
      ss. unfold hide. sim_redE. et.
    - ss. unfold hide. sim_red. sim_tau. sim_red. eapplyfarg step_eval_expr internal_modl ge. i. subst. sim_red. 
      pfold. econs 4.
      { i. inv H0; et. }
      { eexists. econs; et. } i.
      inv STEP; des; clarify. ss. 
      econs 8; et. right. eapply CIH. rewrite GCEQ in H8. 
      determ Clight_eval_expr_determ eval_expr.
      econs; et.
      { change (Maps.PTree.set i _ _) with (set_opttemp (Some i) (map_val sk ge v') tle). eapply match_update_le; et. }
      ss. unfold hide. sim_redE. et. 
    - ss. unfold hide. remove_UBcase. sim_tau. sim_red. eapplyfarg step_eval_expr internal_modl ge. i. sim_red.
      eapply step_eval_exprlist with (ge := ge) (modl:=internal_modl); et. i. remove_UBcase. destruct (nth_error _) eqn: E; remove_UBcase.
      destruct p. remove_UBcase. destruct type_eq.
      2:{ remove_UBcase. }
      pfold. econs 4.
      { i. inv H0; et. }
      { eexists. econs; et. unfold Genv.find_funct. ss. des_ifs. unfold Genv.find_funct_ptr.
        change (Genv.globalenv _) with tge.
        inv MGE. replace b with (Pos.of_succ_nat (pred (Pos.to_nat b))) by nia.
        erewrite ELEM; et. et. } i.
      inv STEP; des; clarify. ss. rewrite GCEQ in H11, H12.
      determ Clight_eval_expr_determ eval_expr.
      determ Clight_eval_exprlist_determ eval_exprlist.
      dup MGE. inv MGE. dup E. apply ELEM in E0. 
      replace (Pos.of_succ_nat (pred (Pos.to_nat b))) with b in E0 by nia.
      apply nth_error_In in E. dup E.

      unfold sk in E1.
      pose proof Sk.le_canon_rev. simpl in H. unfold ClightPlusSkel.incl in *.
      apply H in E1. ss. clear H.
      des.
      Local Transparent ccallU.
      + clarify. ss. unfold ccallU. sim_red. ss. unfold mallocF. repeat (sim_tau; sim_red).
        rewrite PSTATE. sim_red. remove_UBcase. des_ifs_safe. sim_red. unfold unwrapU. remove_UBcase.
        repeat (sim_tau; sim_red). rewrite Any.upcast_downcast. sim_red.

        eapply match_mem_alloc in Heq0; et. clear E. destruct Heq0 as [? [? ?]].
        eapply match_mem_store in Heq1; et. destruct Heq1 as [? [? ?]].
        econs 4.
        { i. inv H3; et. ss. unfold Genv.find_funct_ptr in H13. des_ifs.
          unfold tge in E0 at 1. rewrite Heq0 in E0. clarify. ss. inv H11. et. }
        { unfold Genv.find_funct_ptr in H13. des_ifs.
          change (Genv.globalenv _) with tge in Heq0. rewrite Heq0 in E0. clarify.
          eexists. econs; et. ss.
          replace (Vlong i) with (Vptrofs (Ptrofs.of_int64 i)). 2:{ unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et. }
          econs. { unfold Ptrofs.of_int64. rewrite Ptrofs.unsigned_repr; et. apply Int64.unsigned_range_2. }
          unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et. }
        i.
        unfold Genv.find_funct_ptr in H13. des_ifs.
        change (Genv.globalenv _) with tge in Heq0. rewrite Heq0 in E0. clarify.
        inv STEP. ss. inv H13. unfold Vptrofs in *. des_ifs. unfold Ptrofs.to_int64 in *.
        rewrite Int64.unsigned_repr in H. 2:{ apply Ptrofs.unsigned_range_2. }
        rewrite H in H4. clarify. rewrite H1 in H5. clarify.
        econs 4.
        { i. inv H3; et. }
        { eexists. econs. }
        i. inv STEP. econs 8; et. right. eapply CIH. clear PSTATE. econs; et.
        { change (Vptr _ _) with (map_val sk tge (Vptr b0 Ptrofs.zero)). eapply match_update_le; et. }
        { instantiate (1:=update pstate "Mem" m1↑). et. }
        ss. unfold hide. sim_redE. et.
      + clarify. ss.
        unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold mfreeF. sim_red.
        rewrite PSTATE. sim_tau. sim_red. sim_tau. sim_red. sim_tau. sim_red.
        destruct Archi.ptr64 eqn:?; clarify. destruct vl. { remove_UBcase. }
        destruct v; try solve [remove_UBcase].
        * destruct vl. 2:{ remove_UBcase. } pose proof (Int64.eq_spec i Int64.zero). destruct Int64.eq.
          ** repeat ((repeat sim_red); sim_tau). sim_red. destruct Ptrofs.eq_dec; clarify.
             unfold Genv.find_funct_ptr in H13. des_ifs. 
             change (Genv.globalenv _) with tge in Heq. rewrite Heq in E0. clarify.
             econs 4. { i. inv H. inv H9; et. } { eexists. econs. econs 2. }
             i. inv STEP. inv H8. { unfold Mem.to_ptr in TOPTR. des_ifs. } 
             econs 4. { i. inv H. et. } { eexists. econs. }
             i. inv STEP. econs 8; et. right. apply CIH; et.
             econs; et. 
             { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
             ss. unfold hide. sim_redE. et.
          ** sim_red. remove_UBcase. unfold unwrapU. remove_UBcase. remove_UBcase.
             repeat ((repeat sim_red); sim_tau). sim_red. rewrite Any.upcast_downcast.
             sim_red.
             unfold Genv.find_funct_ptr in H13. des_ifs.
             change (Genv.globalenv _) with tge in Heq3. rewrite Heq3 in E0. clarify.
             hexploit match_mem_denormalize; et. i.
             hexploit match_mem_load; et. i.
             hexploit match_mem_free; et. i. des.
             econs 4. { i. inv H2. inv H13; et. }
             { eexists. econs. econs; et.
              { unfold Mem.to_ptr. rewrite Heq0. rewrite H0. des_ifs. }
              { instantiate (1:= Ptrofs.of_int64 i0). ss. unfold Vptrofs. des_ifs.
                rewrite Ptrofs.to_int64_of_int64; et. }
              { unfold Ptrofs.of_int64. rewrite Ptrofs.unsigned_repr; try nia.
                apply Int64.unsigned_range_2. }
              unfold Ptrofs.of_int64. rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); et.
              apply Int64.unsigned_range_2. }
             i. inv STEP. inv H12. 2:{ unfold Mem.denormalize in H0. apply Maps.PTree.gselectf in H0. des. unfold Mem.denormalize_aux in H2. des_ifs. }
             unfold Mem.to_ptr in TOPTR. des_ifs. unfold Vptrofs in Heq5. des_ifs.
             unfold Ptrofs.to_int64 in TMEM. rewrite Int64.unsigned_repr in TMEM.
             2:{ apply Ptrofs.unsigned_range_2. } rewrite TMEM in H5. clarify.
             econs 4. { i. inv H0. et. } { eexists. econs. }
             i. inv STEP. econs 8; et. right. apply CIH; et.
             econs. 6: et. all: et.
             { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
             { instantiate (1:=update pstate "Mem" m0↑). et. }
             ss. unfold hide. sim_redE. et.
        * destruct vl. 2:{ remove_UBcase. }
          sim_red. remove_UBcase. unfold unwrapU. remove_UBcase. remove_UBcase.
          repeat ((repeat sim_red); sim_tau). sim_red. rewrite Any.upcast_downcast.
          sim_red.
          unfold Genv.find_funct_ptr in H13. des_ifs.
          change (Genv.globalenv _) with tge in Heq1. rewrite Heq1 in E0. clarify.
          hexploit match_mem_load; et. i.
          hexploit match_mem_free; et. i. des.
          econs 4. { i. inv H0. inv H11; et. }
          { eexists. econs. econs; et.
          { instantiate (1:= Ptrofs.of_int64 i0). ss. unfold Vptrofs. des_ifs.
            rewrite Ptrofs.to_int64_of_int64; et. }
          { unfold Ptrofs.of_int64. rewrite Ptrofs.unsigned_repr; try nia.
            apply Int64.unsigned_range_2. }
          unfold Ptrofs.of_int64. rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); et.
          apply Int64.unsigned_range_2. }
          i. inv STEP. inv H9. ss. clarify.
          unfold Vptrofs in Heq. des_ifs. unfold Vptrofs in Heq2. des_ifs.
          unfold Ptrofs.to_int64 in TMEM. rewrite Int64.unsigned_repr in TMEM.
          2:{ apply Ptrofs.unsigned_range_2. } rewrite TMEM in H3. clarify.
          econs 4. { i. inv H. et. } { eexists. econs. }
          i. inv STEP. econs 8; et. right. apply CIH; et.
          econs. 6: et. all: et.
          { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
          { instantiate (1:=update pstate "Mem" m0↑). et. }
          ss. unfold hide. sim_redE. et.
      + apply INTERNAL in E1. des. subst. unfold fnsem_has_internal in WFMS.
        apply WFMS in E. des. unfold ccallU. sim_red. ss. rewrite E. sim_tau. sim_red.
        unfold decomp_func. sim_red. eapplyfarg step_function_entry internal_modl ge.
        i. sim_red.
        unfold Genv.find_funct_ptr in H13. clear E. des_ifs.
        change (Genv.globalenv _) with tge in Heq. rewrite Heq in E0. clarify.
        pfold. econs 4. { i. inv H3; et. } { eexists. econs. et. }
        i. inv STEP. unfold hide in H.
        inv H. inv H8. ss. rewrite <- GCEQ in H6.
        determ alloc_variables_determ alloc_variables.
        econs 8; et. right. eapply CIH. clear PSTATE. econs; et.
        { instantiate (1 := update pstate "Mem" m'↑). et. }
        { econs; et. }
        unfold hide. sim_redE.
        set (prog _) as t1.
        instantiate (1:= mn0).
        apply bind_extk. i. des_ifs_safe. unfold itree_of_cont_pop. sim_redE.
        destruct o0.
        { sim_redE. apply bind_extk. i. des_ifs_safe. sim_redE. f_equal. f_equal.
          sim_redE. et. }
        destruct o1.
        { apply bind_extk. i. des_ifs_safe. sim_redE.
          apply bind_extk. i. sim_redE. f_equal. f_equal. sim_redE. et. }
        sim_redE. f_equal. f_equal. apply bind_extk. i. des_ifs_safe. sim_redE.
        apply bind_extk. i. sim_redE. f_equal. f_equal.
        sim_redE. et. 
    - ss. unfold hide. sim_red. sim_tau. sim_red.
      eapplyf step_eval_exprlist; et.
      { instantiate (1:=internal_modl). et. }
      { instantiate (1:=ge). et. } all: et. i. remove_UBcase.
      + clarify. ss. unfold ccallU. sim_red. ss. unfold mallocF. repeat (sim_tau; sim_red).
        rewrite PSTATE. sim_red. remove_UBcase. des_ifs_safe. sim_red. unfold unwrapU. remove_UBcase.
        repeat (sim_tau; sim_red). rewrite Any.upcast_downcast. sim_red.

        eapply match_mem_alloc in Heq0; et. destruct Heq0 as [? [? ?]].
        eapply match_mem_store in Heq1; et. destruct Heq1 as [? [? ?]].
        econs 4.
        { i. inv H4; et. inv H17. et. }
        { eexists. econs; et.
          replace (Vlong i) with (Vptrofs (Ptrofs.of_int64 i)). 2:{ unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et. }
          econs. { unfold Ptrofs.of_int64. rewrite Ptrofs.unsigned_repr; et. apply Int64.unsigned_range_2. }
          unfold Vptrofs. des_ifs. rewrite Ptrofs.to_int64_of_int64; et. }
        i. ss. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. }
        ss. inv H16. unfold Vptrofs in *. des_ifs.
        determ Clight_eval_exprlist_determ eval_exprlist.
        unfold Ptrofs.to_int64 in *.
        rewrite Int64.unsigned_repr in H0. 2:{ apply Ptrofs.unsigned_range_2. }
        rewrite H0 in H4. clarify.
        econs 8; et. right. apply CIH. clear PSTATE. econs; et.
        { change (Vptr _ _) with (map_val sk tge (Vptr b Ptrofs.zero)). eapply match_update_le; et. }
        { instantiate (1:=update pstate "Mem" m1↑). et. }
        ss. unfold hide. sim_redE. et.
      + clarify. ss.
        unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold mfreeF. sim_red.
        rewrite PSTATE. sim_tau. sim_red. sim_tau. sim_red. sim_tau. sim_red.
        destruct Archi.ptr64 eqn:?; clarify. destruct vl. { remove_UBcase. }
        destruct v; try solve [remove_UBcase].
        * destruct vl. 2:{ remove_UBcase. } pose proof (Int64.eq_spec i Int64.zero). destruct Int64.eq.
          ** repeat ((repeat sim_red); sim_tau). sim_red.
             econs 4. { i. inv H0; et. inv H13; et. } { eexists. econs; et. econs 2. }
             i. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. } 
             inv H12. { determ Clight_eval_exprlist_determ eval_exprlist. }
             econs 8; et. right. apply CIH; et.
             econs; et. 
             { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
             ss. unfold hide. sim_redE. et.
          ** sim_red. remove_UBcase. unfold unwrapU. remove_UBcase. remove_UBcase.
             repeat ((repeat sim_red); sim_tau). sim_red. rewrite Any.upcast_downcast.
             sim_red.
             hexploit match_mem_denormalize; et. i.
             hexploit match_mem_load; et. i.
             hexploit match_mem_free; et. i. des.
             econs 4. { i. inv H3; et. inv H16; et. }
             { eexists. econs; et. econs; et.
              { unfold Mem.to_ptr. rewrite Heq0. rewrite H1. des_ifs. }
              { instantiate (1:= Ptrofs.of_int64 i0). ss. unfold Vptrofs. des_ifs.
                rewrite Ptrofs.to_int64_of_int64; et. }
              { unfold Ptrofs.of_int64. rewrite Ptrofs.unsigned_repr; try nia.
                apply Int64.unsigned_range_2. }
              unfold Ptrofs.of_int64. rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); et.
              apply Int64.unsigned_range_2. }
             i. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. }
             inv H15. 2:{ determ Clight_eval_exprlist_determ eval_exprlist. }
             unfold Mem.to_ptr in TOPTR. des_ifs.
             2:{ determ Clight_eval_exprlist_determ eval_exprlist. }
             determ Clight_eval_exprlist_determ eval_exprlist.
             unfold Vptrofs in Heq. des_ifs.
             unfold Vptrofs in Heq5. des_ifs.
             unfold Ptrofs.to_int64 in TMEM. rewrite Int64.unsigned_repr in TMEM.
             2:{ apply Ptrofs.unsigned_range_2. } rewrite TMEM in H5. clarify.
             econs 8; et. right. apply CIH; et. clear PSTATE.
             econs; et.
             { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
             { instantiate (1:=update pstate "Mem" m0↑). et. }
             ss. unfold hide. sim_redE. et.
        * destruct vl. 2:{ remove_UBcase. }
          sim_red. remove_UBcase. unfold unwrapU. remove_UBcase. remove_UBcase.
          repeat ((repeat sim_red); sim_tau). sim_red. rewrite Any.upcast_downcast.
          sim_red.

          hexploit match_mem_load; et. i.
          hexploit match_mem_free; et. i. des.
          econs 4. { i. inv H1; et. inv H14; et. }
          { eexists. econs; et. econs; et.
          { instantiate (1:= Ptrofs.of_int64 i0). ss. unfold Vptrofs. des_ifs.
            rewrite Ptrofs.to_int64_of_int64; et. }
          { unfold Ptrofs.of_int64. rewrite Ptrofs.unsigned_repr; try nia.
            apply Int64.unsigned_range_2. }
          unfold Ptrofs.of_int64. rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)); et.
          apply Int64.unsigned_range_2. }
          i. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. }
          inv H13.
          2:{ determ Clight_eval_exprlist_determ eval_exprlist. }
          determ Clight_eval_exprlist_determ eval_exprlist.
          ss. clarify.
          unfold Vptrofs in Heq. des_ifs. unfold Vptrofs in Heq1. des_ifs.
          unfold Ptrofs.to_int64 in TMEM. rewrite Int64.unsigned_repr in TMEM.
          2:{ apply Ptrofs.unsigned_range_2. } rewrite TMEM in H3. clarify.
          econs 8; et. right. apply CIH; et. clear PSTATE.
          econs; et.
          { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
          { instantiate (1:=update pstate "Mem" m0↑). et. }
          ss. unfold hide. sim_redE. et.
      + ss. unfold ccallU. sim_red. ss. unfold captureF. sim_tau. sim_red.
        sim_tau. repeat ((repeat sim_red); sim_tau). sim_red. rewrite PSTATE.
        rewrite Any.upcast_downcast. sim_red. remove_UBcase.
        * sim_tau. sim_red.
          econs 4.
          { i. inv H0; et. inv H13; et. determ Clight_eval_exprlist_determ eval_exprlist. }
          { eexists. econs; et. econs. et. }
          i. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. }
          inv H12.
          { determ Clight_eval_exprlist_determ eval_exprlist. }
          { determ Clight_eval_exprlist_determ eval_exprlist. }
          determ Clight_eval_exprlist_determ eval_exprlist.
          econs 8; et. right. apply CIH; et.
          econs; et.
          { change (Vlong n) with (map_val sk tge (Vlong n)). eapply match_update_le; et. }
          ss. unfold hide. sim_redE. et.
        * destruct Coqlib.plt; clarify. unfold Coqlib.Plt in *. ss.
          destruct (classic (exists taddr tm', Mem.capture tm (map_blk sk tge b) taddr tm')).
          ** rewrite bind_trigger.
             econs 6. { ss. }
            { i. inv H1; et. inv H14; et. unfold Mem.capture_oom in OOM. des. exfalso.
              determ Clight_eval_exprlist_determ eval_exprlist.
              red in OOM0. eapply OOM0; et. }
            { des. eexists. econs; et. econs; et. }
            i. inv STEP. ss.
            determ Clight_eval_exprlist_determ eval_exprlist.
            inv H13. 2:{ des; clarify. } 2:{ des; clarify. }
            hexploit match_capture; et. i. des.
            eexists. eexists. { econs. }
            instantiate (1:= (exist _ (addr, m'0) H1)).
            left. sim_red. sim_tau.
            sim_red. sim_tau.
            sim_red. sim_tau.
            sim_red. sim_tau.
            sim_red. sim_tau.
            sim_red. sim_tau.
            sim_red. sim_tau.
            sim_red. econs 8; et. right. apply CIH. des_ifs. clear PSTATE. econs; et.
            { change (Vlong _) with (map_val sk tge (Vlong (Int64.repr (addr + Ptrofs.unsigned i)))). eapply match_update_le; et. }
            { instantiate (1:=update pstate "Mem" m'0↑). et. }
            ss. unfold hide. sim_redE. clear. unfold Vptrofs. des_ifs.
            unfold Ptrofs.to_int64.
            set (Int64.repr _) as t.
            set (Int64.repr _) as t'.
            assert (t = t').
            { unfold t, t'. apply Int64.eqm_samerepr. apply Int64.eqm_sym.
              apply Int64.eqm_unsigned_repr. }
            rewrite H. et.
          ** econs 7.
            { eexists. eexists. econs; et. econs. red.
              split. 2:{ ii. apply H0. et. }
              unfold Mem.valid_block. unfold Coqlib.Plt.
              inv MM. rewrite NBLK. unfold map_blk at 2.
              destruct le_dec; try nia. des_ifs; try nia.
              destruct (Coqlib.plt b (Pos.of_succ_nat (List.length sk))).
              { unfold Coqlib.Plt in p1. hexploit (@map_blk_global_region sk tge b); et.
                nia. i. rewrite <- Pos.ltb_lt. rewrite Pos2Z.inj_ltb. red in H1.
                rewrite <- Pos.ltb_lt in H1. rewrite Pos2Z.inj_ltb in H1. nia. }
              unfold Coqlib.Plt in n. 
              hexploit (@map_blk_local_region sk tge b); et. nia.
              i. unfold map_blk. destruct le_dec; try nia.
              des_ifs; try nia. }
            i. inv H1. 2:{ des; clarify. } 2:{ des; clarify. }
            ss. determ Clight_eval_exprlist_determ eval_exprlist.
            inv H14; et; exfalso. apply H0. et.
    - ss. unfold hide. sim_red. sim_tau.
      econs 4. { i. inv H; et. }
      { eexists. econs. }
      i. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. }
      econs 8; et. right. eapply CIH. econs; et.
      { econs; et. }
      ss. unfold hide. erewrite (number_same_stmt _ _ _ _ _ 2).
      erewrite (number_same_stmt _ _ _ _ _ 3).
      erewrite (number_same_stmt _ _ _ _ _ 1).
      sim_redE. apply bind_extk. i. des_ifs_safe.
      unfold itree_of_cont_pop.
      repeat (des_ifs; sim_redE; try reflexivity).
    - ss. unfold hide. sim_red. sim_tau. sim_red.
      eapplyfarg step_eval_expr internal_modl ge.
      i. eapply step_bool_val with (modl:=internal_modl); et. i.
      pfold. econs 4. { i. inv H2; et. }
      { eexists. econs; et. rewrite H0. et. }
      i. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. }
      econs 8; et. right. eapply CIH. econs; et.
      ss. unfold hide. determ Clight_eval_expr_determ eval_expr.
      erewrite (number_same_stmt _ _ _ _ _ 3).
      erewrite (number_same_stmt _ _ _ _ _ 2).
      repeat (des_ifs; sim_redE; try reflexivity).
    - ss. unfold hide. unfold _sloop_itree. rewrite unfold_itree_iter. unfold hide.
      ss. unfold sloop_iter_body_one. sim_red. sim_tau.
      econs 4. { i. inv H; et. }
      { eexists. econs; et. }
      i. inv STEP. 2:{ des; clarify. } 2:{ des; clarify. }
      econs 8; et. right. eapply CIH. econs; et.
      { econs; et. }
      ss. unfold hide.
      erewrite (number_same_stmt _ _ _ _ _ 4).
      erewrite (number_same_stmt _ _ _ _ _ 5).
      erewrite (number_same_stmt _ _ _ _ _ 1).
      unfold _sloop_itree.
      sim_redE. apply bind_extk. i. 
      unfold itree_of_cont_pop.
      repeat (des_ifs; progress (sim_redE; grind)).
      erewrite (number_same_stmt _ _ _ _ _ 5 _ _ tcode2).
      apply bind_extk. i. des_ifs_safe.
      do 2 (des_ifs; progress (sim_redE; grind)).
      + erewrite (number_same_stmt _ _ _ _ _ 1 _ _ tcode2).
        unfold hide.
        erewrite (number_same_stmt _ _ _ _ _ 2 _ _ tcode1).
        erewrite (number_same_stmt _ _ _ _ _ 3 _ _ tcode2).
        sim_redE. apply bind_extk. i. des_ifs_safe.
      + erewrite (number_same_stmt _ _ _ _ _ 2 _ _ tcode1).
        unfold hide.
        erewrite (number_same_stmt _ _ _ _ _ 1 _ _ tcode2).
        erewrite (number_same_stmt _ _ _ _ _ 3 _ _ tcode2).
        sim_redE. apply bind_extk. i. des_ifs_safe.
      + erewrite (number_same_stmt _ _ _ _ _ 2 _ _ tcode1).
        unfold hide.
        erewrite (number_same_stmt _ _ _ _ _ 1 _ _ tcode2).
        erewrite (number_same_stmt _ _ _ _ _ 3 _ _ tcode2).
        sim_redE. apply bind_extk. i. des_ifs_safe.
      + erewrite (number_same_stmt _ _ _ _ _ 5 _ _ tcode2).
        unfold hide.
        erewrite (number_same_stmt _ _ _ _ _ 2 _ _ tcode1).
        erewrite (number_same_stmt _ _ _ _ _ 1 _ _ tcode2).
        apply bind_extk. i. des_ifs_safe. sim_redE.
        apply bind_extk. i. des_ifs_safe. sim_redE.
        destruct o1.
        * sim_redE. et.
        * sim_redE. do 2 f_equal. sim_redE.
          apply bind_extk. i. des_ifs_safe.
    - ss. unfold hide. destruct tcont; inv MCONT; ss; clarify.
      + sim_red. sim_triggerUB.
      + sim_red. sim_tau. sim_red.
        econs 4. { i. inv H. et. }
        { eexists. econs. }
        i. inv STEP.
        econs 8; et. right. eapply CIH. econs; et. ss. unfold hide. sim_redE. et.
      + sim_tau. sim_red.
        econs 4. { i. inv H; et. }
        { eexists. eapply step_break_loop1. }
        i. inv STEP. { des; clarify. } 
        econs 8; et. right. eapply CIH. econs; et. ss. unfold hide. sim_redE. et.
      + pfold. econs 4. { i. inv H; et. }
        { eexists. eapply step_break_loop2. }
        i. inv STEP. sim_red. sim_tau. sim_red.
        econs 8; et. right. eapply CIH. econs; et. ss. unfold hide. sim_redE. et.
      + sim_red. sim_triggerUB.
    - ss. unfold hide. destruct tcont; inv MCONT; ss; clarify.
      + sim_red. sim_triggerUB.
      + sim_red. sim_tau. sim_red.
        econs 4. { i. inv H. et. }
        { eexists. econs. }
        i. inv STEP.
        econs 8; et. right. eapply CIH. econs; et. ss. unfold hide. sim_redE. et.
      + sim_red. sim_tau. sim_red.
        econs 4. { i. inv H. et. }
        { eexists. econs; et. }
        i. inv STEP.
        econs 8; et. right. eapply CIH. econs; et. { econs; et. } ss. unfold hide. sim_redE. et.
        apply bind_extk. i. sim_redE. des_ifs_safe.
        repeat (des_ifs; sim_redE; try reflexivity).
      + sim_red. sim_triggerUB. 
      + sim_red. sim_triggerUB.
    - ss. unfold hide. unfold _sreturn_c. destruct o; cycle 1.
      + sim_tau. sim_red. eapplyf return_cont; et. i.
        rewrite H0. clear H0. remember (call_cont tcont) as tcont'. 
        inv H; try solve [specialize (call_cont_is_call_cont tcont); rewrite <- H3; clarify].
        * ss. sim_red. eapply step_freeing_stack with (ge := ge) (modl:=internal_modl); et. i.
          sim_red. sim_triggerUB.
        * ss. sim_red. eapply step_freeing_stack with (ge := ge) (modl:=internal_modl); et. i.
          sim_red. sim_tau. sim_red.
          econs 4. { i. inv H1; et. }
          { eexists. econs; et. }
          i. inv STEP. { des; clarify. } 2:{ des; clarify. }
          econs 4. { i. inv H1; et. }
          { eexists. rewrite <- H3. econs; et. }
          i. inv STEP.
          econs 8; et. right. eapply CIH.
          ss. rewrite GCEQ in H8. rewrite H in H8. clarify. rewrite <- H3 in H4. clarify.
          clear PSTATE. econs; et. 
          { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
          { instantiate (1 := update pstate "Mem" m'↑). et. }
          ss. unfold hide. sim_redE. et. 
      + sim_tau. sim_red. eapplyfarg step_eval_expr internal_modl ge.
        i. eapply step_sem_cast with (modl:=internal_modl); et. i. sim_red.
        eapply return_cont; et. i.
        rewrite H3. clear H3 itr_cont''. remember (call_cont tcont) as tcont'.
        inv H2; try solve [specialize (call_cont_is_call_cont tcont); rewrite <- H6; clarify].
        * ss. sim_red. eapply step_freeing_stack with (ge := ge) (modl:=internal_modl); et. i.
          sim_red. remove_UBcase.
          pfold. econs 4. { i. inv H3; et. }
          { eexists. econs; et. }
          i. inv STEP. { des; clarify. } 2:{ des; clarify. }
          ss. rewrite GCEQ in H11. determ Clight_eval_expr_determ eval_expr.
          econs 1.
          2:{ ss. rewrite <- H6. econs. }
          ss. unfold state_sort. ss. rewrite Any.upcast_downcast. et.
        * ss. sim_red. eapply step_freeing_stack with (ge := ge) (modl:=internal_modl); et. i.
          sim_red. sim_tau. sim_red.
          econs 4. { i. inv H3; et. }
          { eexists. econs; et. }
          i. inv STEP. { des; clarify. } 2:{ des; clarify. }
          ss. rewrite GCEQ in H11. determ Clight_eval_expr_determ eval_expr.
          econs 4. { i. inv H; et. }
          { eexists. rewrite <- H6. econs; et. }
          i. inv STEP.
          econs 8; et. right. eapply CIH. clear PSTATE.
          ss. rewrite <- H6 in H1. clarify. econs; et.
          { eapply match_update_le; et. }
          { instantiate (1 := update pstate "Mem" m'↑). et. }
          ss. unfold hide. sim_redE. et.
    (* switch, label, goto is undefined *)
    - ss. unfold hide. sim_triggerUB.
    - ss. unfold hide. sim_triggerUB.
    - ss. unfold hide. sim_triggerUB.
    Unshelve. all: et. all: exact xH.
  Qed.

End PROOF.

