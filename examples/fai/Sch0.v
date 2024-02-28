Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.
Set Typeclasses Depth 5.




Section PROOF.
  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_evnetE: eventE -< Es}.
    Context `{has_schE: schE -< Es}.
    Context `{has_callE: callE -< Es}.
    Context (sk: Sk.t).

    Definition spawnF: string * val -> itree Es nat :=
      fun varg =>
        let '(fn, args) := varg in
        trigger (Spawn fn args↑).

    Definition yieldF: () -> itree Es () :=
      fun _ => trigger Yield.

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



  Definition SchSem (sk : Sk.t) : ModSem.t :=
    {|
      ModSem.fnsems := [("_spawn", cfunU spawnF) ; ("_yield", cfunU yieldF)
      (* ("thread_yield", cfunU yieldF);
                        ("get_curid", cfunU getpidF); ("thread_create", cfunU (thread_createF sk)) *)
                        ];
      ModSem.init_st := tt↑;
    |}
  .

  Definition Sch: Mod.t := {|
    Mod.get_modsem := SchSem;
    Mod.sk := [];
    (* [("thread_yield", (Cgfun (Tfunction Tnil tvoid cc_default))↑);
               ("get_curid", (Cgfun (Tfunction Tnil tint cc_default))↑);
               ("thread_create", (Cgfun (Tfunction
                                           (Tcons (tptr tint)
                                              (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
                                                 (Tcons (tptr tvoid) Tnil))) tint cc_default))↑)]; *)
  |}
  .
End PROOF.