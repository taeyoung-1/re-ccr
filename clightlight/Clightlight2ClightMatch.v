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
  
  Import List.

  Local Open Scope Z.


  (* global env is fixed when src program is fixed *)
  Variable sk : Sk.t.
  Variable tge : Genv.t Clight.fundef type.

  (* composite env should be fixed when src program is fixed*)
  Variable ce : composite_env.

  (* ModSem should be fixed with src too *)
  Variable ms : ModSemL.t.

  (* should never appear *)
  Definition dummy_blk : positive := 1%positive.

  Definition le_dec (p1 p2 : positive) : { Pos.le p1 p2 } + { not (Pos.le p1 p2) }. 
  Proof.
    destruct (p1 <=? p2)%positive eqn: E.
    - left. eapply Pos.leb_le; et.
    - right. eapply Pos.leb_gt in E; nia.
  Qed.

  Definition map_blk : positive -> Values.block :=
    fun blk =>
      if (le_dec (Pos.of_succ_nat (length sk)) blk)%positive
      then 
        match Zpos blk + (Z.pos tge.(genv_next) - Z.pos (Pos.of_succ_nat (length sk))) with
        | Zpos tblk => tblk
        | _ => dummy_blk (* unreachable *)
        end
      else
        let sg := Sk.load_skenv sk in
        match sg.(SkEnv.blk2id) (pred (Pos.to_nat blk)) with
        | Some name =>
          match Genv.find_symbol tge (ident_of_string name) with
          | Some tblk => tblk
          | None => dummy_blk
          end
        | None => dummy_blk
        end
  .

  Definition map_val (v : val) : val :=
    match v with
    | Vptr blk ofs => Vptr (map_blk blk) ofs
    | _ => v
    end.

  Definition map_memval (mv : memval) : memval :=
    match mv with
    | Fragment v q n => Fragment (map_val v) q n
    | _ => mv
    end.

  Variant match_ge : Prop :=
  | match_ge_intro
      (WFSK: Sk.wf sk)
      (MGE: forall id idx, SkEnv.id2blk (Sk.load_skenv sk) (string_of_ident id) = Some idx -> Genv.find_symbol tge id = Some (map_blk (Pos.of_succ_nat idx)))
      (ELEM: forall s n gd, nth_error sk n = Some (s, gd↑) -> Genv.find_def tge (map_blk (Pos.of_succ_nat n)) = Some gd)
    :
      match_ge.

  Variant match_le : temp_env -> temp_env -> Prop :=
  | match_le_intro
      sle tle 
      (ML: forall id sv, Maps.PTree.get id sle = Some sv -> Maps.PTree.get id tle = Some (map_val sv))
    :
      match_le sle tle.

  Definition map_env_entry (entry: ident * (Values.block * type)) :=
    let '(id, (b, ty)) := entry in
    (id, (map_blk b, ty)).

  Variant match_e : env -> env -> Prop :=
  | match_e_intro
      se te 
      (ME: forall a, In a (Maps.PTree.elements te) <-> In a (List.map map_env_entry (Maps.PTree.elements se)))
    :
      match_e se te.
  
  Lemma env_match_some e te id b ty (ME: match_e e te) :
    e ! id = Some (b, ty) -> te ! id = Some (map_blk b, ty).
  Proof.
    i. apply PTree.elements_correct in H. inv ME.
    apply PTree.elements_complete. rewrite ME0.
    rewrite in_map_iff. eexists; split; et. ss.
  Qed.

  Lemma env_match_none e te id (ME: match_e e te) :
    e ! id = None -> te ! id = None.
  Proof.
    i. destruct (te ! id) eqn : E; et. 
    apply PTree.elements_correct in E. inv ME. rewrite ME0 in E.
    rewrite in_map_iff in E. des. destruct x. 
    apply PTree.elements_complete in E0. unfold map_env_entry in *.
    destruct p0. clarify.
  Qed.

  Definition map_entry (entry1 entry2: Values.block * type) : Prop :=
    entry1 = (let (b, ty) := entry2 in (map_blk b, ty)).

  Lemma match_env_same e te (ME: match_e e te) 
    : 
  Maps.PTree.elements te = List.map map_env_entry (Maps.PTree.elements e).
  Proof.
    hexploit (Maps.PTree.elements_canonical_order map_entry te e).
    - i. inv ME. apply PTree.elements_correct in H. rewrite ME0 in H.
      rewrite in_map_iff in H. des. destruct x0 as [? [? ?]].
      ss. clarify. exists (b, t0). split; ss; et.
      apply PTree.elements_complete; et.
    - i. inv ME. apply PTree.elements_correct in H.
      eapply in_map in H. rewrite <- ME0 in H. ss. destruct y.
      eexists. split; ss; et. apply Maps.PTree.elements_complete. et.
    - i. set (Maps.PTree.elements te) as l in *.
      set (Maps.PTree.elements e) as l' in *. clearbody l l'.
      induction H; ss. des. f_equal; et. unfold map_env_entry.
      unfold map_entry in *. des_ifs. ss. clarify. rewrite <- H1.
      destruct a1. et. 
  Qed.

  Variant match_mem : Memory.Mem.mem -> Memory.Mem.mem -> Prop :=
  | match_mem_intro
      m tm
      (INITIALIZED: (Pos.of_succ_nat (length sk) <= m.(Mem.nextblock))%positive)
      (NBLK: tm.(Mem.nextblock) = map_blk (m.(Mem.nextblock)))
      (MEM_CNT: forall b ofs mv, PMap.get ofs (PMap.get b m.(Mem.mem_contents)) = mv -> PMap.get ofs (PMap.get (map_blk b) tm.(Mem.mem_contents)) = map_memval mv)
      (MEM_PERM: forall b, PMap.get b m.(Mem.mem_access) = Maps.PMap.get (map_blk b) tm.(Mem.mem_access) )
    :
      match_mem m tm.

End MATCH.
