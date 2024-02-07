Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import Imp.

Set Implicit Arguments.

Definition nullptr := Vptr 0 0%Z.

Definition printVint: list val -> itree Es val :=
  fun varg =>
    `v: Z <- (pargs [Tint] varg)?;;
    _ <- trigger (Syscall "print" [v]↑ top1) ;;
    Ret Vundef
  .

Definition printVptr: list val -> itree Es val :=
  fun varg =>
    '(blk, ofs) <- (pargs [Tptr] varg)?;;
    _ <- trigger (Syscall "print" [(Z.of_nat blk); ofs]↑ top1) ;;
    Ret Vundef
  .

  Definition printV v := 
    match v with
    | Vint x => printVint [v]
    | Vptr b ofs => printVptr [v]
    | _ => printVint [v]
    end
    .