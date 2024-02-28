Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.

Set Implicit Arguments.
Set Typeclasses Depth 8.




Section PROOF.
  Section BODY.
    Context `{Es: Type -> Type}.
    Context `{has_evnetE: eventE -< Es}.
    Context `{has_schE: schE -< Es}.
    Context `{has_callE: callE -< Es}.
    Context (sk: Sk.t).
    Context `{Σ : GRA.t}.

    Definition spawnF: string * val -> itree Es nat :=
      fun varg =>
        let '(fn, args) := varg in
        trigger (Spawn fn args↑).

    (* lee: should invariant dependent on input? *)
    Definition spawn_spec: fspec :=
      (mk_simple (fun I => (
                      ord_top,
                      (fun varg => I),
                      (fun vret => I)
      ))).


    Definition yieldF: () -> itree Es () :=
      fun _ => trigger Yield.

    (* lee: should invariant dependent on input? *)
    Definition yield_spec: fspec :=
      (mk_simple (fun I => (
                      ord_top,
                      (fun varg => I),
                      (fun vret => I)
      ))).

    (* Definition getpidF: (list val) -> itree Es val :=
      fun varg =>
        match varg with
        | [] =>
            pid <- trigger EventsL.Getpid;;
            Ret (Vint (Int.repr (Z.of_nat pid)))
        | _ => triggerUB
        end.
    
    Definition thread_createF: list val -> itree Es val :=
      fun varg =>
        match varg with
        | [Vptr bid ofsid;Vptr bf ofsf;Vptr barg ofsarg] =>
            '(gsym, gdata) <- (nth_error sk (pred (Pos.to_nat bf)))?;;
            gd <- (gdata↓)?;;
            _ <- (match gd with Cgfun fd => Some fd | _ => None end)?;;
            `v_pid : val <- ccallU "spawn" (gsym, [Vptr barg ofsarg]);;
            `_ : unit <- ccallU "store" (Mint16signed, Vptr bid ofsid, v_pid);;
            Ret (Vint Int.zero)
        | _ => triggerUB
        end. *)

  End BODY.

  Context `{Σ : GRA.t}.

  Definition SchStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("_spawn", spawn_spec) ; ("_yield", yield_spec)].
  Defined.

  Definition SchSbtb: list (gname * fspecbody) :=
    [("_spawn", mk_specbody spawn_spec (cfunU spawnF));
    ("_yield",   mk_specbody yield_spec (cfunU yieldF))]
  .

  Definition SSchSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := SchSbtb;
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SSch: SMod.t := {|
    SMod.get_modsem := SSchSem;
    SMod.sk := Sk.unit;
  |}
  .

  (* lee: should stb be variable? *)
  Definition Sch: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SSch.

End PROOF.