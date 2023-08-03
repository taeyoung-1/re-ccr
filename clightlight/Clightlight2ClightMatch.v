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

  Context `{Σ: GRA.t}.
  
  Definition itree_of_Es_format {A} (es_itree: itree Es A) (ms: ModSemL.t) (mn: string) (rp: p_state) :=
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

  Variant match_ge defs : SkEnv.t -> (Genv.t (Ctypes.fundef function) type) -> Prop :=
  | match_ge_intro
      sge tge
      (MG: forall gn idx,
          (sge.(SkEnv.id2blk) gn = Some idx) ->
          (Genv.find_symbol tge (ident_of_string gn) = Some (map_blk defs (Pos.of_succ_nat idx))))
    :
      match_ge defs sge tge.

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

  Definition itree_of_code (mn: string) (retty: type) (code: statement) (e: env) (le: temp_env) : stateT p_state (itree eventE) (env * temp_env * option bool * option val) := 
    EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (decomp_stmt sk ce retty code e le)).

  Definition itree_of_cont (mn: string) (retty: type) (k: cont) (e: env) (le: temp_env) (optb: option bool) (optv: option val) : stateT p_state (itree eventE) val := 
    EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (decomp_cont sk ce retty k e le optb optv)).

  Variant match_states defs : itree eventE Any.t -> Clight.state -> Prop :=
  | match_states_intro
      tf pstate e te le tle tcode m tm tcont mn itr_code itr_cont
      (ML: @match_le defs le tle)
      (PSTATE: pstate "Mem"%string = m↑)
      (MM: @match_mem defs m tm)
      (MCODE: itr_code = itree_of_code mn tf.(fn_return) tcode e le pstate)
      (MCONT: itr_cont = itree_of_cont mn tf.(fn_return) tcont)
    :
      match_states defs ('(pstate', (e', le', optb, optv)) <- itr_code;; '(_, v) <- itr_cont e' le' optb optv pstate';; Ret v↑) (State tf tcode tcont te tle tm)
  .

End MATCH.
