From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Values Maps.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ConvC2ITree.
Require Import Clight_Mem0.

Set Implicit Arguments.

From compcert Require Import Ctypes Clight Clightdefs Globalenvs.
Import Genv.

Section MATCH.

  Context `{Σ: GRA.t}.
  
  Definition Es_to_eventE {A} (ms: ModSemL.t) (mn: string) (es_itree: itree Es A) (rp: p_state) :=
     EventsL.interp_Es (ModSemL.prog ms) (transl_all mn es_itree) rp.

  (* should never appear *)
  Definition dummy_blk : positive := 1%positive.

  Definition map_blk (defs: list (AST.ident * AST.globdef Clight.fundef Ctypes.type)) : positive -> Values.block :=
    fun blk =>
      if (ge_dec (Pos.to_nat blk) (S (List.length (get_sk defs))))
      then Pos.of_nat ((List.length defs - List.length (get_sk defs)) + (Pos.to_nat blk))
      else
        let sg := Sk.load_skenv (get_sk defs) in
        let tg := Genv.add_globals (Genv.empty_genv _ _ (List.map fst defs)) defs  in
        match sg.(SkEnv.blk2id) (pred (Pos.to_nat blk)) with
        | Some name =>
          match Genv.find_symbol tg (ident_of_string name) with
          | Some tblk => tblk
          | None => dummy_blk
          end
        | None => dummy_blk
        end
  .

  Definition map_val defs (v : val) : val :=
    match v with
    | Vptr blk ofs => Vptr (map_blk defs blk) ofs
    | _ => v
    end.

  Definition map_memval defs (mv : memval) : memval :=
    match mv with
    | Fragment v q n => Fragment (map_val defs v) q n
    | _ => mv
    end.

  Variant match_le defs : temp_env -> temp_env -> Prop :=
  | match_le_intro
      sle tle 
      (ML: forall id sv, Maps.PTree.get id sle = Some sv -> Maps.PTree.get id tle = Some (map_val defs sv))
    :
      match_le defs sle tle.

  Variant match_e defs : env -> env -> Prop :=
  | match_e_intro
      se te 
      (ME: forall id b ty, se ! id = Some (b, ty) <-> te ! id = Some (map_blk defs b, ty))
    :
      match_e defs se te.

  Variant match_ge defs : Sk.t -> Genv.t (Ctypes.fundef function) type -> Prop :=
  | match_ge_intro
      sk ge
      (PUBLIC_INCL: forall s, In s (List.map fst sk) -> In (ident_of_string s) ge.(genv_public))
      (S2B_MATCH: forall s n, (do '(blk, _) <- find_idx (fun '(s', _) => string_dec s s') sk; Some blk) = Some n -> ge.(genv_symb) ! (ident_of_string s) = Some (map_blk defs (Pos.of_succ_nat n)))
      (B2D_MATCH: forall s n agd, nth_error sk n = Some (s, agd) -> exists gd, ge.(genv_defs) ! (map_blk defs (Pos.of_succ_nat n)) = Some gd /\ Any.downcast agd = Some gd)
      (NEXT_MATCH: ge.(genv_next) = map_blk defs (Pos.of_succ_nat (List.length sk)))
    :
      match_ge defs sk ge.

  (* global env is fixed when src program is fixed *)
  Variable sk : Sk.t.
  (* composite env should be fixed when src program is fixed*)
  Variable ce : composite_env.
  (* ModSem should be fixed with src too *)
  Variable ms : ModSemL.t.


  Variant match_mem defs : Memory.Mem.mem -> Memory.Mem.mem -> Prop :=
  | match_mem_intro
      m tm
      (INITIALIZED: Pos.to_nat m.(Mem.nextblock) >= (List.length (get_sk defs)))
      (NBLK: tm.(Mem.nextblock) = map_blk defs (m.(Mem.nextblock)))
      (MEM_CNT: forall b ofs mv, PMap.get ofs (PMap.get b m.(Mem.mem_contents)) = mv -> PMap.get ofs (PMap.get (map_blk defs b) tm.(Mem.mem_contents)) = map_memval defs mv )
      (MEM_PERM: forall b, PMap.get b m.(Mem.mem_access) = Maps.PMap.get (map_blk defs b) tm.(Mem.mem_access) )
    :
      match_mem defs m tm
  .

  Definition itr_t := itree Es runtime_env.

  (* clightlight state should be expressed by two constructs, stmt and cont *)
  Definition clightlight_state := itree eventE Any.t.

  Definition itree_of_code (mn: string) (retty: type) (code: statement) (e: env) (le: temp_env) 
    : stateT p_state (itree eventE) runtime_env 
      := Es_to_eventE ms mn (decomp_stmt sk ce retty code e le).

  Definition ktree_of_cont_itree (mn: string) (cont_itr: runtime_env -> itr_t)
    : p_state * runtime_env -> itree eventE (p_state * runtime_env) 
      := fun '(pstate, ncr) => Es_to_eventE ms mn (cont_itr ncr) pstate.

  Definition itree_of_cont_pop (itr_sreturn: itr_t) (itr_sbreak: itr_t) (itr_scontinue: itr_t) (itr_skip: itr_t) 
  : option bool -> option val -> itr_t :=
    fun optb optv =>
      match optv with
      | Some _ => itr_sreturn
      | None =>
        match optb with
        | Some true => itr_sbreak
        | Some false => itr_scontinue
        | None => itr_skip
        end
      end.

  Definition kstop_itree (ncr: runtime_env) : itree Es val := 
    let '(e, le, optb, optv) := ncr in
      '(_, _, _, optv') <- (itree_of_cont_pop 
                              (free_list_aux (ConvC2ITree.blocks_of_env ce e);;; Ret (e, le, None, optv)) 
                              triggerUB 
                              triggerUB 
                              triggerUB) optb optv;; 
      v <- optv'?;; (match v with | Vint _ => Ret v | _ => triggerUB end).

  Definition itree_stop (mn: string) := fun '(pstate, ncr) => Es_to_eventE ms mn (kstop_itree ncr) pstate.

    (* below is functional version of continuation translation *)
    (*
  Fixpoint decomp_cont (retty: type) (k: Clight.cont) (e: env) (le: temp_env) (optb: option bool) (optv: option val) : itree eff val :=
    match k with
    | Kseq code k' => 
      '(e', le', optb', optv') <- (treat_flow 
                                    (Ret (e, le, None, optv)) 
                                    (Ret (e, le, optb, None)) 
                                    (Ret (e, le, optb, None)) 
                                    (decomp_stmt retty code e le)) optb optv;;
      decomp_cont retty k' e' le' optb' optv'
    | Kloop1 code1 code2 k' => 
      '(e', le', optb', optv') <- (treat_flow 
                                    (Ret (e, le, None, optv)) 
                                    (Ret (e, le, None, None)) 
                                    ('(e2, le2, ov2) <- sloop_iter_body_two (decomp_stmt retty code2 e le);;
                                     match ov2 with
                                     | Some v2 => Ret (e2, le2, None, v2)
                                     | None => _sloop_itree e2 le2 (decomp_stmt retty code1) (decomp_stmt retty code2)
                                     end)
                                    ('(e2, le2, ov2) <- sloop_iter_body_two (decomp_stmt retty code2 e le);;
                                     match ov2 with
                                     | Some v2 => Ret (e2, le2, None, v2)
                                     | None => _sloop_itree e2 le2 (decomp_stmt retty code1) (decomp_stmt retty code2)
                                     end)) optb optv;;
      decomp_cont retty k' e' le' optb' optv'
    | Kloop2 code1 code2 k' =>
      '(e, le, ov2) <- (match optv with 
                        | Some v => Ret (e, le, Some (Some v)) 
                        | None => 
                          match optb with 
                          | Some true => Ret (e, le, Some None)
                          | Some false => triggerUB
                          | None => Ret (e, le, None)
                          end
                        end);;
      '(e', le', optb', optv') <- (match ov2 with
                                  | Some v2 => Ret (e, le, None, v2)
                                  | None => _sloop_itree e le (decomp_stmt retty code1) (decomp_stmt retty code2)
                                  end);;
      decomp_cont retty k' e' le' optb' optv'
    | Kstop => 
      '(_, _, _, optv') <- (treat_flow 
                            (free_list_aux (blocks_of_env ce e);;; Ret (e, le, None, optv)) 
                            triggerUB 
                            triggerUB 
                            triggerUB) optb optv;;
      v <- optv'?;; (match v with Vint _ => Ret v | _ => triggerUB end)
    | Kcall optid f e' le' k' =>
      '(_, _, _, optv') <- (treat_flow 
                            (free_list_aux (blocks_of_env ce e);;; tau;; Ret (e, le, None, optv)) 
                            triggerUB 
                            triggerUB 
                            (free_list_aux (blocks_of_env ce e);;; tau;; Ret (e, le, None, Some Vundef))) optb optv;;
      v <- optv'?;; decomp_cont f.(fn_return) k' e' (set_opttemp optid v le') None None
    | _ => triggerUB
    end.
     *)

(* mname is just module name pops the continuation *)
  Inductive match_cont defs : type -> mname -> (p_state * runtime_env -> itree eventE (p_state * val)) -> cont -> Prop := 
  | match_cont_Kseq cont_itree next code cont retty mn
      (ITR: cont_itree = ktree_of_cont_itree mn 
                        (fun '(e, le, optb, optv) => 
                          (itree_of_cont_pop
                            (Ret (e, le, None, optv)) 
                            (Ret (e, le, optb, None)) 
                            (Ret (e, le, optb, None)) 
                            (decomp_stmt sk ce retty code e le)) optb optv))
      (NEXT: match_cont defs retty mn next cont)
    :
      match_cont defs retty mn (fun x => y <- cont_itree x;; next y) (Kseq code cont)
  | match_cont_Kloop1 cont_itree next code1 code2 cont retty mn
      (ITR: cont_itree = ktree_of_cont_itree mn
                        (fun '(e, le, optb, optv) => 
                          (itree_of_cont_pop
                            (Ret (e, le, None, optv)) 
                            (Ret (e, le, None, None)) 
                            ('(e2, le2, ov2) <- sloop_iter_body_two (decomp_stmt sk ce retty code2 e le);;
                              match ov2 with
                              | Some v2 => Ret (e2, le2, None, v2)
                              | None => _sloop_itree e2 le2 (decomp_stmt sk ce retty code1) (decomp_stmt sk ce retty code2)
                              end)
                            ('(e2, le2, ov2) <- sloop_iter_body_two (decomp_stmt sk ce retty code2 e le);;
                              match ov2 with
                              | Some v2 => Ret (e2, le2, None, v2)
                              | None => _sloop_itree e2 le2 (decomp_stmt sk ce retty code1) (decomp_stmt sk ce retty code2)
                              end)) optb optv))
      (NEXT: match_cont defs retty mn next cont) 
    :
      match_cont defs retty mn (fun x => y <- cont_itree x;; next y) (Kloop1 code1 code2 cont)
  | match_cont_Kloop2 cont_itree next code1 code2 cont retty mn
      (ITR: cont_itree = ktree_of_cont_itree mn
                        (fun '(e, le, optb, optv) => 
                          '(e, le, ov2) <- 
                            (match optv with 
                            | Some v => Ret (e, le, Some (Some v)) 
                            | None => match optb with 
                                      | Some true => Ret (e, le, Some None)
                                      | Some false => triggerUB
                                      | None => Ret (e, le, None)
                                      end
                            end);;
                          match ov2 with
                          | Some v2 => Ret (e, le, None, v2)
                          | None => _sloop_itree e le (decomp_stmt sk ce retty code1) (decomp_stmt sk ce retty code2)
                          end))
      (NEXT: match_cont defs retty mn next cont) 
    :
      match_cont defs retty mn (fun x => y <- cont_itree x;; next y) (Kloop2 code1 code2 cont)
  | match_cont_Kstop cont_itree retty mn
      (ITR: cont_itree = itree_stop mn)
    :
      match_cont defs retty mn cont_itree Kstop
  | match_cont_Kcall cont_itree next optid f e' le' te' tle' cont retty mn_caller mn_callee
      (ITR: cont_itree = ktree_of_cont_itree mn_callee
                        (fun '(e, le, optb, optv) => 
                          '(_, _, _, optv') <-
                            (itree_of_cont_pop
                              (free_list_aux (ConvC2ITree.blocks_of_env ce e);;; tau;; Ret (e, le, None, optv)) 
                              triggerUB 
                              triggerUB 
                              (free_list_aux (ConvC2ITree.blocks_of_env ce e);;; tau;; Ret (e, le, None, Some Vundef))) optb optv;;
                          v <- optv'?;; Ret (e', set_opttemp optid v le', None, None))) 
      (CONT_ENV_MATCH: match_e defs e' te')
      (CONT_LENV_MATCH: match_le defs le' tle')
      (NEXT: match_cont defs f.(fn_return) mn_caller next cont) 
    :
      match_cont defs retty mn_callee (fun x => y <- cont_itree x;; next y) (Kcall optid f te' tle' cont).
  

  Variant match_states defs : itree eventE Any.t -> Clight.state -> Prop :=
  | match_states_intro
      tf pstate e te le tle tcode m tm tcont mn itr_code itr_cont itr
      (ML: @match_le defs le tle)
      (ME: @match_e defs e te)
      (PSTATE: pstate "Mem"%string = m↑)
      (MM: @match_mem defs m tm)
      (MCODE: itr_code = itree_of_code mn tf.(fn_return) tcode e le pstate)
      (MCONT: match_cont defs tf.(fn_return) mn itr_cont tcont)
      (MENTIRE: itr = x <- itr_code;; '(_, v) <- itr_cont x;; Ret v↑)
    :
      match_states defs itr (State tf tcode tcont te tle tm)
  .

End MATCH.
