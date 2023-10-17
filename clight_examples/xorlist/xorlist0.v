Require Import ConvC2ITree.
Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import xorlist.
From compcertip Require Import Values.

(* TODO: start xorlist proof *)
Definition globenv := Clight.globalenv prog.
Definition encrypt_body : list val -> itree Es val  := decomp_func globenv f_encrypt.
Definition decrypt_body : list val -> itree Es val  := decomp_func globenv f_decrypt.
Definition delete_body : list val -> itree Es val  := decomp_func globenv f_delete.
Definition insert_body : list val -> itree Es val  := decomp_func globenv f_insert.

Definition xorSbtb :=
  [("encrypt",  cfunU encrypt_body);
   ("decrypt",  cfunU decrypt_body);
   ("insert",  cfunU insert_body);
   ("delete",  cfunU delete_body)].

Definition xorSem : ModSem.t :=
  {|
    ModSem.fnsems := xorSbtb;
    ModSem.mn := "xorlist";
    ModSem.initial_st := tt↑;
  |}.

Definition xor : Mod.t :=
  {|
    Mod.get_modsem := fun _ => xorSem;
    Mod.sk := Sk.unit;
  |}.