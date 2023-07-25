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

From compcert Require Import Ctypes Clight Clightdefs.

Section MATCH.

  Fixpoint get_cont_stmts (cc: cont) : list statement :=
    match cc with
    | Kseq s k => s :: (get_cont_stmts k)
    | _ => []
    end
  .

(*   Fixpoint wf_ccont (k: cont) : Prop :=
    match k with
    | Kseq s k2 =>
      match s with
      | Sreturn _ =>
        match k2 with
        | Kstop => True
        | Kcall _ _ env _ k3 => (env = empty_env /\ wf_ccont k3)
        | _ => False
        end
      | _ => wf_ccont k2
      end
    | _ => False
    end
  . *)

  Fixpoint get_cont_stack k : option cont :=
    match k with
    | Kseq s k2 => get_cont_stack k2
    | Kcall _ _ _ _ _ => Some k
    | _ => None 
    end
  .
(*
  Lemma wf_cont_has_stack
        k
        (WFCCONT: wf_ccont k)
    :
      exists ks, get_cont_stack k = Some ks.
  Proof.
    revert_until k.
    induction k; i; ss; clarify.
    destruct s; ss; clarify; eauto.
    destruct k; ss; clarify; eauto.
  Qed. *)

  Context `{Σ: GRA.t}.
  
  Definition itree_of_Es_format {A} (es_itree: itree Es A) (ms: ModSemL.t) (mn: string) (rp: p_state) :=
     EventsL.interp_Es (ModSemL.prog ms) (transl_all mn es_itree) rp.

  (* Definition itree_of_stmt (sk: Sk.t) (ce: composite_env) (ms: ModSem.t) (mn: string) (retty: type) :=
    fun code e le rp =>
     itree_of_Es_format (decomp_stmt sk ce retty code e le) ms mn rp.

  Fixpoint itree_of_stmts (sk: Sk.t) (ce: composite_env) (ms: ModSem.t) (mn: string) (retty: type) (stmts: list statement) :=
    match stmts with
    | [] => (fun e le p => Ret (p, (e, le, None, ))
    | a :: l =>
          fun e le p =>
            ((p', (e', le', bc, v)) <- (itree_of_stmt sk ce ms mn retty a e le p);;
            match v with
            | Some retval =>
              Ret (e', le', None, v)
            | None =>
              match bc with
              | None =>
                (itree_of_stmts sk ce ms mn l retty e' le' p')
              | Some _ => Ret (e', le', bc, None)
              end
            end)
    end.
    itree_of_stmt
    fun sk ce rettype code e le ms mn rp =>
      EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (decomp_stmt sk ce rettype code e le)) rp. *)
(*
  Definition itree_of_imp_ret :=
    fun ge le ms mn rp =>
      itree_of_imp_cont (denote_expr (Var "return"%string)) ge le ms mn rp.

  Lemma itree_of_imp_cont_bind
        T R ge le ms mn rp (itr: itree _ T) (ktr: T -> itree _ R)
    :
      itree_of_imp_cont (x <- itr;; ktr x) ge le ms mn rp
      =
      '(p, (le2, v)) <- (itree_of_imp_cont itr ge le ms mn rp);; (itree_of_imp_cont (ktr v) ge le2 ms mn (p)).
  Proof.
    unfold itree_of_imp_cont. rewrite interp_imp_bind. grind.
    rewrite! transl_all_bind; rewrite! EventsL.interp_Es_bind.
    grind. destruct p0. grind.
  Qed.

  Definition itree_of_imp_pop :=
    fun ge ms mn retmn (retx: var) (retle: lenv) (x: _ * (lenv * val)) =>
      let '(p, (le0, _)) := x in
      '(p2, rv) <- EventsL.interp_Es (ModSemL.prog ms) (transl_all mn ('(_, v) <- interp_imp ge (denote_expr (Var "return"%string)) le0;; Ret (v↑))) (p);;
      '(p3, rv) <- EventsL.interp_Es (ModSemL.prog ms) ((tau;; Ret rv)) (p2);;
      pop <- EventsL.interp_Es (ModSemL.prog ms) (transl_all retmn (tau;; tau;; v0 <- unwrapU (rv↓);; (tau;; tau;; tau;; Ret (alist_add retx v0  retle, Vundef)))) (p3);;
      Ret pop.

  Definition itree_of_imp_pop_bottom :=
    fun ms mn (x : p_state * (lenv * val)) =>
      ` x0 : p_state * Any.t <-
      (let (st1, v) := x in
      EventsL.interp_Es (ModSemL.prog ms)
                        (transl_all mn (` x0 : val <- (let (_, retv) := v in Ret retv);; Ret (Any.upcast x0))) st1);; Ret (snd x0).

  Definition itree_of_cont_stmt (s : Imp.stmt) :=
    fun ge le ms mn rp => itree_of_imp_cont (denote_stmt s) ge le ms mn rp.

  Definition imp_state := itree eventE Any.t.
  Definition imp_cont {T} {R} := (p_state * (lenv * T)) -> itree eventE (p_state * (lenv * R)).
  Definition imp_stack := (p_state * (lenv * val)) -> imp_state.

  (* Hypothesis archi_ptr64 : Archi.ptr64 = true. *)
  Context `{builtins : builtinsTy}.

  Definition ext_len : Imp.programL -> nat := fun src => List.length (src.(ext_varsL)) + List.length (src.(ext_funsL)).
  Definition int_len : Imp.programL -> nat := fun src => List.length (src.(prog_varsL)) + List.length (src.(prog_funsL)).
  Definition sk_len : Imp.programL -> nat := fun src => List.length src.(defsL).
  (* next block of src's initialized genv *)
  Definition src_init_nb : Imp.programL -> nat := fun src => sk_len src.
  (* next block of tgt's initialized genv *)
  Definition tgt_init_len := List.length ((@init_g builtins) ++ c_sys).
  Definition tgt_init_nb : Imp.programL -> Values.block := fun src => Pos.of_succ_nat (tgt_init_len + (ext_len src) + (int_len src)).

  Definition get_sge (src : Imp.programL) := Sk.load_skenv (Sk.sort (ImpMod.get_modL src).(ModL.sk)).
  Definition get_tge (tgt : Csharpminor.program) := Genv.globalenv tgt.

 *)
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

  Variant match_ge defs : SkEnv.t -> (Genv.t fundef ()) -> Prop :=
  | match_ge_intro
      sge tge
      (MG: forall gn idx,
          (sge.(SkEnv.id2blk) gn = Some idx) ->
          (Genv.find_symbol tge (ident_of_string gn) = Some (map_blk defs (Pos.of_succ_nat idx))))
    :
      match_ge defs sge tge.
(*
  Definition return_stmt := Sreturn (Some (Evar (s2p "return"))).
  Definition ret_call_cont k := Kseq return_stmt (call_cont k).

  Definition exit_stmt := Sreturn (Some (Eunop Cminor.Ointoflong (Evar (s2p "return")))).
  Definition ret_call_main := Kseq exit_stmt Kstop.

  (* global env is fixed when src program is fixed *)
  Variable ge : SkEnv.t.
  (* ModSem should be fixed with src too *)
  Variable ms : ModSemL.t.

  Inductive match_code (mn: mname) : imp_cont -> (list Csharpminor.stmt) -> Prop :=
  | match_code_exit
    :
      match_code mn (fun '(p, (le, _)) => itree_of_imp_ret ge le ms mn (p)) [exit_stmt]
  | match_code_return
    :
      match_code mn idK [return_stmt]
  | match_code_cont
      code itr ktr chead ctail
      (CST: compile_stmt code = chead)
      (ITR: itr = fun '(p, (le, _)) => itree_of_cont_stmt code ge le ms mn (p))
      (MCONT: match_code mn ktr ctail)
    :
      match_code mn (fun x => (itr x >>= ktr)) (chead :: ctail)
  .

  Inductive match_stack (src: Imp.programL) (mn: mname) : imp_stack -> option Csharpminor.cont -> Prop :=
  | match_stack_bottom
    :
      match_stack src mn (itree_of_imp_pop_bottom ms mn) (Some ret_call_main)

  | match_stack_cret
      tf le tle next stack tcont id tid tpop retmn
      (MLE: @match_le src le tle)
      (MID: s2p id = tid)

      (WFCONT: wf_ccont tcont)
      (MCONT: match_code retmn next (get_cont_stmts tcont))
      (MSTACK: match_stack src retmn stack (get_cont_stack tcont))

      (TPOP: tpop = ret_call_cont (Kcall (Some tid) tf empty_env tle tcont))
    :
      match_stack src mn (fun x => (y <- (itree_of_imp_pop ge ms mn retmn id le x);; next y >>= stack)) (Some tpop)
  .
 *)

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

(*   Variant match_states src : imp_state -> Csharpminor.state -> Prop :=
  | match_states_intro
      tf pstate le tle code itr tcode m tm next stack tcont mn
      (CST: compile_stmt code = tcode)
      (ML: @match_le src le tle)
      (PSTATE: pstate "Mem"%string = m↑)
      (MM: @match_mem src m tm)
      (WFCONT: wf_ccont tcont)
      (MCONT: next = itree_of_stmts (get_cont_stmts tcont))
      (MSTACK: @match_stack src mn stack (get_cont_stack tcont))
      (ITR: body = itree_of_stmt sk ce rettype tcode e le ms mn pstate)
    :
      match_states src (x <- body;; next x >>= stack) (State tf tcode tcont te tle tm)
  . *)

End MATCH.
