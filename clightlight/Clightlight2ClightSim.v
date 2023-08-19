From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ConvC2ITree.
Require Import SimSTS3.
Require Import Clight_Mem0.
Require Import IRed.

Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightArith.
Require Import Clightlight2ClightLenv.
Require Import Clightlight2ClightMem.

From compcert Require Import Ctypes Clight Clightdefs Values.

Lemma unbind_trigger E:
  forall [X0 X1 A : Type] (ktr0 : X0 -> itree E A) (ktr1 : X1 -> itree E A) e0 e1,
    (x <- trigger e0;; ktr0 x = x <- trigger e1;; ktr1 x) -> (X0 = X1 /\ e0 ~= e1 /\ ktr0 ~= ktr1).
Proof.
  i. eapply f_equal with (f:=_observe) in H. cbn in H.
  inv H. split; auto.
  dependent destruction H3. dependent destruction H2.
  cbv in x. subst. split; auto.
  assert (ktr0 = ktr1); clarify.
  extensionality x. eapply equal_f in x0.
  rewrite ! subst_bind in *.
  irw in x0. eauto.
Qed.

Lemma angelic_step :
  forall (X : Prop) (ktr next : itree eventE Any.t),
    ModSemL.step (trigger (Take X);;; ktr) None next -> (next = ktr /\ X).
Proof.
  i. dependent destruction H; try (irw in x; clarify; fail).
  rewrite <- bind_trigger in x. apply unbind_trigger in x.
  des. clarify.
Qed.

(* Lemma eval_exprlist_length :
  forall a b c d l1 l2
    (EE: eval_exprlist a b c d l1 l2),
    <<EELEN: List.length l1 = List.length l2>>.
Proof.
  i. induction EE; ss; clarify; eauto.
Qed. *)

Section PROOF.

  Import ModSemL.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Definition compile_val md := @ModL.compile _ EMSConfigC md. 

  Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Clight.program) => @sim_mon (compile_val src) (Clight.semantics2 tgt)).
  Hint Resolve _sim_mon: paco.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (step_tau _).

  Definition arrow (A B: Prop): Prop := A -> B.
  Opaque arrow.

  Definition oeq [A] (a: A) b: Prop := (a = b).
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

  Ltac tgt_step := try pfold; econs 4; eexists; eexists; [|left].

  Ltac wrap_up := try pfold; econs 7; et; right.

  Ltac remove_UBcase := des_ifs; try sim_red; try sim_triggerUB.

  Ltac eapplyf NEXT := let X := fresh "X" in hexploit NEXT;[..|intro X; punfold X; et].
  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

  Local Opaque Pos.of_nat.

  Local Opaque Pos.of_succ_nat.

  Lemma step_load pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    chunk addr
    tf tcode tcont ktr b r mn
    (NEXT: forall v,
            Mem.loadv chunk tm (map_val sk tge addr) = Some (map_val sk tge v) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * val <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "load" (chunk, addr))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. 
    sim_tau. ss. sim_red. unfold loadF. repeat (sim_red; sim_tau). sim_red.
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. sim_tau. sim_red. rewrite Any.upcast_downcast.
    sim_red. eapplyf NEXT. unfold Mem.loadv in *. des_ifs_safe. ss. clarify. hexploit match_mem_load; et.
  Qed.
  
    

  Lemma step_store pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    chunk addr v
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m',
            Mem.storev chunk tm (map_val sk tge addr) (map_val sk tge v) = Some tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * () <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "store" (chunk, addr, v))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold storeF. sim_red. repeat (sim_tau; sim_red).
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. repeat (sim_tau; sim_red). rewrite Any.upcast_downcast.
    sim_red. unfold Mem.storev in Heq. des_ifs_safe. hexploit match_mem_store; et. i. des. eapplyf NEXT; et. 
  Qed.

  Lemma step_loadbytes pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    blk ofs n
    tf tcode tcont ktr b r mn
    (NEXT: forall l,
            Mem.loadbytes tm (map_blk sk tge blk) (Ptrofs.unsigned ofs) n = Some (List.map (map_memval sk tge) l) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, l))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * list memval <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "loadbytes" (Vptr blk ofs, n))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold loadbytesF. repeat (sim_red; sim_tau). sim_red.
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. sim_tau. sim_red. rewrite Any.upcast_downcast.
    sim_red. eapplyf NEXT. hexploit match_mem_loadbytes; et.
  Qed.

  Lemma step_storebytes pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    blk ofs l
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m',
            Mem.storebytes tm (map_blk sk tge blk) (Ptrofs.unsigned ofs) (List.map (map_memval sk tge) l) = Some tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * () <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "storebytes" (Vptr blk ofs, l))) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold storebytesF. sim_red. repeat (sim_tau; sim_red).
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. repeat (sim_tau; sim_red). rewrite Any.upcast_downcast.
    sim_red. hexploit match_mem_storebytes; et. i. des. eapplyf NEXT; et.
  Qed.

  Lemma step_load_bitfield pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    ty sz sg pos width addr
    tf tcode tcont ktr b r mn
    (NEXT: forall v,
            Cop.load_bitfield ty sz sg pos width tm (map_val sk tge addr) (map_val sk tge v)->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (load_bitfield_c ty sz sg pos width addr)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold load_bitfield_c.
    remove_UBcase; eapply step_load; et;
      i; remove_UBcase; eapplyf NEXT; econs; try nia; try des_ifs.
  Qed.

  Lemma step_store_bitfield pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    ty sz sg pos width addr v
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m' v',
            match_mem sk tge m' tm' ->
            Cop.store_bitfield ty sz sg pos width tm (map_val sk tge addr) (map_val sk tge v) tm' (map_val sk tge v')->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (store_bitfield_c ty sz sg pos width addr v)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold store_bitfield_c. remove_UBcase;
      eapply step_load; et; i; remove_UBcase; 
        eapply step_store; et; i; sim_red;
          eapplyf NEXT; et; econs; et; try nia; des_ifs.
  Qed.

  Lemma step_weak_valid_pointer pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    blk ofs
    tf tcode tcont ktr bflag r mn
    (NEXT: forall b,
            (Mem.weak_valid_pointer tm (map_blk sk tge blk) ofs = b) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true bflag
              (ktr (pstate, b))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true bflag
      (`r0: (p_state * bool) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (weak_valid_pointer_c blk ofs)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold weak_valid_pointer_c, ccallU. sim_red. sim_tau. ss. unfold valid_pointerF. sim_red. 
    repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
    unfold valid_pointerF. sim_red. repeat (sim_tau; sim_red). rewrite PSTATE.
    sim_red. repeat (sim_tau; sim_red). eapplyf NEXT; et.
    unfold Mem.weak_valid_pointer, Mem.valid_pointer. inv MM.
    repeat (match goal with | |- context ctx [ Mem.perm_dec ?x ] => destruct (Mem.perm_dec x) end); et;
      ss; unfold Mem.perm in *; rewrite <- MEM_PERM in *; contradiction.
  Qed.

  Lemma step_sem_cast pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    v ty1 ty2
    tf tcode tcont ktr b r mn
    (NEXT: forall optv,
            (optv = None -> Cop.sem_cast (map_val sk tge v) ty1 ty2 tm = None) ->
            (forall v', optv = Some v' -> Cop.sem_cast (map_val sk tge v) ty1 ty2 tm = Some (map_val sk tge v')) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, optv))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * option val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (sem_cast_c v ty1 ty2)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold sem_cast_c. des_ifs_safe. des_ifs.
    all: try solve [sim_red; eapplyf NEXT; i; clarify; ss; unfold Cop.sem_cast; des_ifs].
    sim_red. eapply step_weak_valid_pointer; et. i. 
      des_ifs; sim_red; eapplyf NEXT; et; ss; i; clarify;
       unfold Cop.sem_cast; rewrite Heq1; des_ifs_safe. 
  Qed.

  Lemma divide_c_divides a b : (a > 0)%Z -> (divide_c a b = true <-> (a | b)).
  Proof.
    split; i; unfold divide_c in *.
    - rewrite Z.eqb_eq in H0. econs; et.
    - inv H0. rewrite Z_div_mult; try nia.
  Qed.

  Lemma step_assign_loc pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    ty blk ofs bf v
    tf tcode tcont ktr b r mn ce
    (NEXT: forall tm' m',
            match_mem sk tge m' tm' ->
            assign_loc ce ty tm (map_blk sk tge blk) ofs bf (map_val sk tge v) tm' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * ())<- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (assign_loc_c ce ty blk ofs bf v)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold assign_loc_c. des_ifs; try sim_red; try sim_triggerUB.
    2,3,6,7 : eapply step_store_bitfield; et; i; sim_red; eapplyf NEXT; et; econs; et.
    - eapply step_store; et. i. des. eapplyf NEXT; et. econs; et. 
    - eapply step_loadbytes; et. i. eapply step_storebytes; et. i.
      eapplyf NEXT; et. destruct (_ && _) eqn: E in Heq0; clarify.
      apply andb_true_iff in E. des. econs 2; et; i.
      1,2: rewrite <- divide_c_divides; et; pose proof alignof_blockcopy_pos; et.
      destruct (_||_) eqn: E1 in Heq1 ; clarify. repeat rewrite orb_true_iff in E1.  
      des; try nia. left. destruct (b0 =? blk)%positive eqn:E2 in E1; clarify.
      apply Pos.eqb_neq in E2. red. i. apply E2. eapply map_blk_inj; et; admit "".
    - eapply step_loadbytes; et. i. eapply step_storebytes; et. i.
      eapplyf NEXT; et. econs 2; et; i; try nia.
  Qed.

  Lemma step_deref_loc pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    ty blk ofs bf
    tf tcode tcont ktr b r mn
    (NEXT: forall v,
            deref_loc ty tm (map_blk sk tge blk) ofs bf (map_val sk tge v) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (deref_loc_c ty blk ofs bf)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold deref_loc_c. destruct bf.
    - remove_UBcase.
      + eapply step_load; et. i. eapplyf NEXT; ss; econs; et.
      + eapplyf NEXT; ss; econs 2; et.
      + eapplyf NEXT; ss; econs 3; et.
    - des_ifs; eapply step_load_bitfield; et; i; eapplyf NEXT; econs; ss.
  Qed.

  (* Lemma sk_In sk s n : SkEnv.id2blk (Sk.load_skenv sk) s = Some n -> In s (List.map fst sk).
  Proof.
    Transparent Sk.load_skenv. ss. uo. des_ifs. i. clarify. Opaque Sk.load_skenv.
    unfold find_idx in Heq0. set 0 as i in Heq0. clearbody i.
    depgen i. revert s p0 n. induction sk; i; clarify.
    ss. destruct a. destruct p0. ss. destruct (string_dec s s0); et.
    right. ss. eapply IHsk; et.
  Qed.   *)

  Lemma step_unary_op pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    uop v ty 
    tf tcode tcont ktr b r mn
    (NEXT: forall optv,
            (optv = None -> Cop.sem_unary_operation uop (map_val sk tge v) ty tm = None) ->
            (forall v', optv = Some v' -> Cop.sem_unary_operation uop (map_val sk tge v) ty tm = Some (map_val sk tge v')) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, optv))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * option val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (unary_op_c uop v ty)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold unary_op_c. des_ifs; sim_red.
    - unfold bool_val_c. des_ifs.
      all: try solve [sim_red; eapplyf NEXT; i; clarify; ss; unfold Cop.sem_unary_operation; des_ifs; 
                unfold Cop.sem_notbool, Cop.bool_val; des_ifs].
      all: try (unfold Values.Val.of_bool; ss; des_ifs).
      1,2,4,5: sim_red; eapplyf NEXT; i; clarify; ss; unfold Cop.sem_unary_operation; des_ifs; 
                unfold Cop.sem_notbool, Cop.bool_val; des_ifs; bsimpl; clarify.
      sim_red. eapply step_weak_valid_pointer; et. i. 
      destruct b1; sim_red; eapplyf NEXT; et; i; clarify;
        unfold Cop.sem_notbool, Cop.bool_val; des_ifs.
    - eapplyf NEXT; i;
        unfold Cop.sem_unary_operation, Cop.sem_notint in *; des_ifs; ss; clarify.
    - eapplyf NEXT; i;
        unfold Cop.sem_unary_operation, Cop.sem_neg in *; des_ifs; ss; clarify.
    - eapplyf NEXT; i;
        unfold Cop.sem_unary_operation, Cop.sem_absfloat in *; des_ifs; ss; clarify.
  Qed.

  Lemma step_binary_op pstate f_table modl cprog sk tge ce le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    biop v1 ty1 v2 ty2
    tf tcode tcont ktr b r mn
    (NEXT: forall optv,
            (optv = None -> Cop.sem_binary_operation ce biop (map_val sk tge v1) ty1 (map_val sk tge v2) ty2 tm = None) ->
            (forall retv, optv = Some retv -> Cop.sem_binary_operation ce biop (map_val sk tge v1) ty1 (map_val sk tge v2) ty2 tm = Some (map_val sk tge retv)) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, optv))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * option val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (binary_op_c ce biop v1 ty1 v2 ty2)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold binary_op_c. des_ifs; unfold sem_add_c, sem_sub_c, sem_mul_c, sem_div_c, sem_mod_c, sem_and_c, sem_or_c, sem_xor_c, Cop.sem_shl, Cop.sem_shr, sem_cmp_c; try sim_red.
    - des_ifs; try sim_red;
        try (eapplyf NEXT; i; ss;
            unfold Cop.sem_add; rewrite Heq; unfold Cop.sem_add_ptr_int, Cop.sem_add_ptr_long in *; 
            des_ifs; ss; clarify).
      unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_add; rewrite Heq; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_add; rewrite Heq; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_add; rewrite Heq; unfold Cop.sem_binarith; 
          rewrite Heq0 in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
    - des_ifs; try sim_red;
        try (eapplyf NEXT; i; ss; unfold Cop.sem_sub; rewrite Heq; des_ifs; ss; clarify).
      + eapply map_blk_inj in e0; et. contradiction.
      + 
      unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_sub; rewrite Heq; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_sub; rewrite Heq; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_sub; rewrite Heq; unfold Cop.sem_binarith; 
          rewrite Heq0 in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_mul; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_mul; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_mul; unfold Cop.sem_binarith; 
          rewrite Heq in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_div; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_div; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_div; unfold Cop.sem_binarith; 
          rewrite Heq in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss;
            rewrite Heq0; ss.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_mod; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_mod; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_mod; unfold Cop.sem_binarith; 
          rewrite Heq in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss;
            rewrite Heq0; ss.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_and; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_and; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_and; unfold Cop.sem_binarith; 
          rewrite Heq in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss;
            rewrite Heq0; ss.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_or; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_or; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_or; unfold Cop.sem_binarith; 
          rewrite Heq in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss;
            rewrite Heq0; ss.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_xor; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_xor; unfold Cop.sem_binarith;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_xor; unfold Cop.sem_binarith; 
          rewrite Heq in *; try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss;
            rewrite Heq0; ss.
    - eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_shl; unfold Cop.sem_binarith; 
        unfold Cop.sem_shift in *; des_ifs; ss; clarify.
    - eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_shr; unfold Cop.sem_binarith; 
        unfold Cop.sem_shift in *; des_ifs; ss; clarify.
    - des_ifs; unfold cmp_ptr_c; try sim_red; des_ifs_safe; 
        try solve [unfold cmplu_bool_c; des_ifs; try sim_red; try eapplyf NEXT; i; ss; clarify; 
                    unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2,3: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapplyf NEXT; i; ss; clarify. unfold Cop.sem_cmp. rewrite Heq. unfold Cop.cmp_ptr. des_ifs_safe. ss.
          unfold Val.of_bool. des_ifs.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          try solve [repeat (destruct (Mem.perm_dec _) in Heq3); inv MM; unfold Mem.perm in *; ss;
                      rewrite <- MEM_PERM in *; try contradiction].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          try solve [repeat (destruct (Mem.perm_dec _) in Heq3); inv MM; unfold Mem.perm in *; ss;
                      rewrite <- MEM_PERM in *; try contradiction].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          try solve [repeat (destruct (Mem.perm_dec _) in Heq3); inv MM; unfold Mem.perm in *; ss;
                      rewrite <- MEM_PERM in *; try contradiction].
    + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [ eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; 
          rewrite Heq in *; rewrite Heq0 in *;
            try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
      all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
    - des_ifs; unfold cmp_ptr_c; try sim_red; des_ifs_safe; 
        try solve [unfold cmplu_bool_c; des_ifs; try sim_red; try eapplyf NEXT; i; ss; clarify; 
                    unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2,3: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapplyf NEXT; i; ss; clarify. unfold Cop.sem_cmp. rewrite Heq. unfold Cop.cmp_ptr. des_ifs_safe. ss.
          unfold Val.of_bool. des_ifs.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          try solve [repeat (destruct (Mem.perm_dec _) in Heq3); inv MM; unfold Mem.perm in *; ss;
                      rewrite <- MEM_PERM in *; try contradiction].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          try solve [repeat (destruct (Mem.perm_dec _) in Heq3); inv MM; unfold Mem.perm in *; ss;
                      rewrite <- MEM_PERM in *; try contradiction].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          try solve [repeat (destruct (Mem.perm_dec _) in Heq3); inv MM; unfold Mem.perm in *; ss;
                      rewrite <- MEM_PERM in *; try contradiction].
    + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [ eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; 
          rewrite Heq in *; rewrite Heq0 in *;
            try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
      all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
    - des_ifs; unfold cmp_ptr_c; try sim_red; des_ifs_safe; 
        try solve [unfold cmplu_bool_c; des_ifs; try sim_red; try eapplyf NEXT; i; ss; clarify; 
                    unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2,3: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapplyf NEXT; i; ss; clarify. unfold Cop.sem_cmp. rewrite Heq. unfold Cop.cmp_ptr. des_ifs_safe. ss.
          unfold Val.of_bool. des_ifs.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
    + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [ eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; 
          rewrite Heq in *; rewrite Heq0 in *;
            try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
      all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
    - des_ifs; unfold cmp_ptr_c; try sim_red; des_ifs_safe; 
        try solve [unfold cmplu_bool_c; des_ifs; try sim_red; try eapplyf NEXT; i; ss; clarify; 
                    unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2,3: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapplyf NEXT; i; ss; clarify. unfold Cop.sem_cmp. rewrite Heq. unfold Cop.cmp_ptr. des_ifs_safe. ss.
          unfold Val.of_bool. des_ifs.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
    + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [ eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; 
          rewrite Heq in *; rewrite Heq0 in *;
            try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
      all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
    - des_ifs; unfold cmp_ptr_c; try sim_red; des_ifs_safe; 
        try solve [unfold cmplu_bool_c; des_ifs; try sim_red; try eapplyf NEXT; i; ss; clarify; 
                    unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2,3: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapplyf NEXT; i; ss; clarify. unfold Cop.sem_cmp. rewrite Heq. unfold Cop.cmp_ptr. des_ifs_safe. ss.
          unfold Val.of_bool. des_ifs.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
    + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [ eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; 
          rewrite Heq in *; rewrite Heq0 in *;
            try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
      all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
    - des_ifs; unfold cmp_ptr_c; try sim_red; des_ifs_safe; 
        try solve [unfold cmplu_bool_c; des_ifs; try sim_red; try eapplyf NEXT; i; ss; clarify; 
                    unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2,3: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapplyf NEXT; i; ss; clarify. unfold Cop.sem_cmp. rewrite Heq. unfold Cop.cmp_ptr. des_ifs_safe. ss.
          unfold Val.of_bool. des_ifs.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          eapplyf NEXT; i; ss; clarify;
            unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *; des_ifs_safe.
          unfold Val.of_bool; ss. des_ifs.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
          1: eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe.
          2: eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
          all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
      + unfold cmplu_bool_c; des_ifs; try sim_red;
          try solve [eapplyf NEXT; i; ss; clarify; unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; des_ifs_safe].
        * eapply step_weak_valid_pointer; et; i; des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
                unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; 
                  unfold Mem.weak_valid_pointer in *; clarify.
        * eapply step_weak_valid_pointer; et. i. sim_red. eapply step_weak_valid_pointer; et. i.
          des_ifs; sim_red; eapplyf NEXT; i; ss; clarify;
          unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; des_ifs_safe; unfold Mem.weak_valid_pointer in *; clarify;
          unfold Val.of_bool; des_ifs. 
        * unfold ccallU. sim_red. ss. repeat (sim_tau; sim_red). unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          unfold valid_pointerF. sim_red.
          repeat (sim_tau; sim_red). rewrite PSTATE. sim_red. repeat (sim_tau; sim_red).
          repeat match goal with | |- context [Mem.perm_dec ?x ?y ?z ?w ?a] => destruct (Mem.perm_dec x y z w a) end; sim_red;
            eapplyf NEXT; i; ss; clarify;
              unfold Cop.sem_cmp; rewrite Heq; unfold Cop.cmp_ptr; ss; unfold Mem.valid_pointer in *;
                destruct (eq_block _); des_ifs_safe;
          try solve [eapply map_blk_inj in e0; et; try contradiction];
          repeat (destruct (Mem.perm_dec _)); inv MM; unfold Mem.perm in *; ss.
    + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. destruct optv; sim_red;
        try solve [ eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      eapply step_sem_cast; et. i. destruct optv; try sim_red;
        try solve [eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; rewrite Heq;
                  try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss].
      des_ifs; sim_red; 
        eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_cmp; unfold Cop.sem_binarith; 
          rewrite Heq in *; rewrite Heq0 in *;
            try (erewrite H by et); try (erewrite H0 by et); try (erewrite H1 by et); try (erewrite H2 by et); ss.
      all: unfold Val.of_bool; unfold Val.cmplu_bool; des_ifs; unfold Int64.cmpu; rewrite Heq1; ss.
  Qed.

  Lemma _step_eval pstate ge ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: ce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a
 :
  (forall ktr1,
    (forall blk ofs bf, 
      eval_lvalue ge te tle tm a (map_blk sk tge blk) ofs bf ->
      paco4
        (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
        (ktr1 (pstate, (blk, (ofs, bf))))
        (State tf tcode tcont te tle tm)) 
    ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * (Values.block * (ptrofs * bitfield))) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a)) 
          pstate);; ktr1 r0)
      (State tf tcode tcont te tle tm)) 
  /\
  (forall ktr2,
    (forall v, 
      eval_expr ge te tle tm a (map_val sk tge v) ->
      paco4
        (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
        (ktr2 (pstate, v))
        (State tf tcode tcont te tle tm)) 
    ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * Values.val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr2 r0)
      (State tf tcode tcont te tle tm)). 
  Proof.
    induction a.
    1,2,3,4 : split; i; remove_UBcase; eapply H; try econs.
    9,10 : des; split; i; remove_UBcase; ss; unfold Vptrofs; 
          eapply H; et; des_ifs_safe; econs.
    2,4,5,6,7 : des; split; i; remove_UBcase; ss.
    - split; i; ss.
      + remove_UBcase; eapply H; et. 
        * econs. eapply env_match_some in ME; et.
        * econs 2; try solve [eapply env_match_none; et]. inv MGE. eapply MGE0; et.
      + remove_UBcase; eapply step_deref_loc; et; i; sim_red; eapply H; et; econs; et.
        * econs. hexploit env_match_some; et.
        * econs 2; try solve [eapply env_match_none; et]. inv MGE. eapply MGE0; et.
    - unfold unwrapU. remove_UBcase. eapply H; et. econs. inv MLE. eapply ML. et.
    - eapply IHa. i. subst. destruct bf; try sim_red; try sim_triggerUB. eapply H; et. econs; et.
    - eapply IHa0. i. sim_red. eapply step_unary_op; et. i. sim_red.
      destruct optv; try sim_triggerUB. sim_red. eapply H; et. econs; et.
    - eapply IHa3. i. sim_red. eapply IHa0. i. sim_red. eapply step_binary_op; et.
      i. sim_red. destruct optv; try sim_triggerUB. sim_red. eapply H; et. econs; et.
    - eapply IHa0. i. sim_red. eapply step_sem_cast; et. i.
      sim_red. unfold unwrapU. remove_UBcase. eapply H; et. econs; et. 
    - des; split; i; ss; remove_UBcase; eapply IHa0; i; remove_UBcase.
      + eapply H. econs; et.
      + eapply step_deref_loc; et. i. sim_red. eapply H. econs; et. econs;et.
    - des. split; i; ss; sim_red; eapply IHa0; i; subst. 
      + remove_UBcase; unfold unwrapU; remove_UBcase; remove_UBcase; eapply H; et; [econs|econs 5]; et.
      + remove_UBcase; unfold unwrapU; remove_UBcase; remove_UBcase; 
        eapply step_deref_loc; et; i; sim_red; eapply H; et; econs; et; [econs|econs 5]; et.
  Qed.
    

  Lemma step_eval_lvalue pstate ge ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: ce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall blk ofs bf, 
            eval_lvalue ge te tle tm a (map_blk sk tge blk) ofs bf ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, (blk, (ofs, bf))))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * (Values.block * (ptrofs * bitfield))) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof. hexploit _step_eval; et. i. des. et. Qed.

  Lemma step_eval_expr pstate ge ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: ce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall v v', 
            eval_expr ge te tle tm a v ->
            v = map_val sk tge v' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * Values.val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm). 
  Proof. hexploit _step_eval; et. i. des. et. Qed.
          

End PROOF.