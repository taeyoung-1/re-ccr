(* Require Import ZArith String List Lia. *)

Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight Clightdefs.


Global Program Instance EMSConfigC: EMSConfig := {|
  finalize := fun rv =>
                match rv↓ with
                | Some (rv) =>
                  match rv with
                  | Vint z => Some z↑
                  | _ => None
                  end
                | _ => None
                end;
  initial_arg := ([]: list val)↑;
|}
.
Definition admit (excuse: String.string) {T: Type} : T.  Admitted.
Tactic Notation "admit" constr(excuse) := idtac excuse; exact (admit excuse).

Section GType.
  
  Inductive C_SkelEntry:=
  | Cgfun (function_type: type)
  | Cgvar (gv: globvar type)
  .

End GType.

Section Clight.
Context {eff : Type -> Type}.
Context {HasCall : callE -< eff}.
Context {HasEvent : eventE -< eff}.
Variable sk: Sk.t.
Let skenv: SkEnv.t := Sk.load_skenv sk.
Variable ce: composite_env.
  
Section EVAL_EXPR_COMP.

  Local Open Scope Z.
  
  Definition divide_c (n m: Z): bool :=
    let x := m / n in
    (x * n =? m).

  Definition assign_loc_c (ce: composite_env)
           (ty: type) (b: block) (ofs: ptrofs)
           (v: val): itree eff unit :=
  match access_mode ty with
  | By_value chunk =>
    ccallU "store" (chunk, Vptr b ofs, v)
  | By_copy =>
    match v with
    | Vptr b' ofs' =>
      let chk1 :=
          if (0 <? sizeof ce ty) then
            andb (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs'))
                 (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs))
          else true in
      if negb chk1 then Ret tt else
        let chk2 :=
            (orb (negb (b' =? b))%positive
                 (orb (Ptrofs.unsigned ofs' =? Ptrofs.unsigned ofs)
                      (orb (Ptrofs.unsigned ofs' + sizeof ce ty <=? Ptrofs.unsigned ofs)
                           (Ptrofs.unsigned ofs + sizeof ce ty <=? Ptrofs.unsigned ofs'))))%Z
        in
        if negb chk2 then Ret tt else
          bytes <- @ccallU _ _ _ _ (option (list memval))
                           "loadbytes" (Vptr b' ofs', sizeof ce ty);;
          ccallU "storebytes" (Vptr b ofs, bytes)
    | _ => Ret tt
    end
  | By_reference => Ret tt
  | By_nothing => Ret tt
  end.

  Definition deref_loc_c (ty: type)
             (b:block) (ofs: ptrofs): itree eff (option val) :=
    match access_mode ty with
    | By_value chunk => (v <- ccallU "load" (chunk, Vptr b ofs);; Ret(Some v) )
    | By_reference => Ret (Some (Vptr b ofs))
    | By_copy => Ret (Some (Vptr b ofs))
    | By_nothing => Ret None
    end.

  Variable e: Clight.env.
  Variable le: Clight.temp_env.

  Section EVAL_LVALUE.
    Variable _eval_expr_c: expr -> itree eff (option val).

    Definition _eval_lvalue_c (a: expr)
      : itree eff (option (block * (ptrofs * bitfield))) :=
      match a with
      | Evar id ty =>
        match e ! id with
        | Some (l, ty') =>
          if type_eq ty ty' then Ret (Some (l, (Ptrofs.zero, Full)))
          else Ret None
        | None =>
          match SkEnv.id2blk skenv (string_of_ident id) with
          | Some i => Ret (Some (Pos.of_nat (S i), (Ptrofs.zero, Full)))
          | None => Ret None
          end
        end
      | Ederef a ty =>
        v <- _eval_expr_c a;;
        match v with
        | Some (Vptr l ofs) => Ret (Some (l, (ofs, Full)))
        | _ => Ret None
        end
      | Efield a i ty =>
        v <- _eval_expr_c a;;
        match v with
        | Some (Vptr l ofs) =>
          match Clight.typeof a with
          | Tstruct id att =>
            match ce ! id with
            | Some co =>
              match field_offset ce i (co_members co) with
              | Errors.OK (delta, bf) =>
                Ret (Some (l, (Ptrofs.add ofs (Ptrofs.repr delta), bf)))
              | _ => Ret None
              end
            | _ => Ret None
            end
          | Tunion id att =>
            match ce ! id with
            | Some co =>
                match union_field_offset ce i (co_members co) with
                | Errors.OK (delta, bf) =>
                    Ret (Some (l, ((Ptrofs.add ofs (Ptrofs.repr delta)), bf)))
                | _ => Ret None
                end
            | None => Ret None
            end
          | _ => Ret None
          end
        | _ => Ret None
        end
      | _ => Ret None
      end.

  End EVAL_LVALUE.

  Definition weak_valid_pointer_c (b: block) (ofs: Z): itree eff bool:=
    b1 <- ccallU "valid_pointer" (b, ofs);;
    b2 <- ccallU "valid_pointer" (b, (ofs - 1)%Z);;
    Ret (b1 || b2).
  
  Definition bool_val_c v ty: itree eff (option bool) :=
    match Cop.classify_bool ty with
    | Cop.bool_case_i =>
      match v with
      | Vint n => Ret (Some (negb (Int.eq n Int.zero)))
      | Vptr b ofs =>
        if Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b (Ptrofs.unsigned ofs);;
          if (ret: bool)
          then Ret (Some true)
          else Ret None
      | _ => Ret None
      end
    | Cop.bool_case_l =>
      match v with
      | Vlong n => Ret (Some (negb (Int64.eq n Int64.zero)))
      | Vptr b ofs =>
        if negb Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b (Ptrofs.unsigned ofs);;
          if (ret: bool)
          then Ret (Some true)
          else Ret None
      | _ => Ret None
      end
    | Cop.bool_case_f =>
      match v with
      | Vfloat f => Ret (Some (negb (Floats.Float.cmp Ceq f Floats.Float.zero)))
      | _ => Ret None
      end
    | Cop.bool_case_s =>
      match v with
      | Vsingle f => Ret (Some (negb (Floats.Float32.cmp Ceq f Floats.Float32.zero)))
      | _ => Ret None
      end
    | Cop.bool_default => Ret None
    end
  .

  Definition unary_op_c op v ty: itree eff (option val) :=
    match op with
    | Cop.Onotbool =>
      v <- bool_val_c v ty;; Ret (Coqlib.option_map (Val.of_bool ∘ negb) v)
    | Cop.Onotint => Ret (Cop.sem_notint v ty)
    | Cop.Oneg => Ret (Cop.sem_neg v ty)
    | Cop.Oabsfloat => Ret (Cop.sem_absfloat v ty)
    end
  .

  Definition sem_cast_c v t1 t2: itree eff (option val) :=
    match Cop.classify_cast t1 t2 with
    | Cop.cast_case_pointer =>
      match v with
      | Vint _ => if Archi.ptr64 then Ret None else Ret (Some v)
      | Vlong _ => if Archi.ptr64 then Ret (Some v) else Ret None
      | Vptr _ _ => Ret (Some v)
      | _ => Ret None
      end
    | Cop.cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Ret (Some (Vint (Cop.cast_int_int sz2 si2 i)))
      | _ => Ret None
      end
    | Cop.cast_case_f2f =>
      match v with
      | Vfloat f => Ret (Some (Vfloat f))
      | _ => Ret None
      end
    | Cop.cast_case_s2s =>
      match v with
      | Vsingle f => Ret (Some (Vsingle f))
      | _ => Ret None
      end
    | Cop.cast_case_f2s =>
      match v with
      | Vfloat f => Ret (Some (Vsingle (Floats.Float.to_single f)))
      | _ => Ret None
      end
    | Cop.cast_case_s2f =>
      match v with
      | Vsingle f => Ret (Some (Vfloat (Floats.Float.of_single f)))
      | _ => Ret None
      end
    | Cop.cast_case_i2f si1 =>
      match v with
      | Vint i => Ret (Some (Vfloat (Cop.cast_int_float si1 i)))
      | _ => Ret None
      end
    | Cop.cast_case_i2s si1 =>
      match v with
      | Vint i => Ret (Some (Vsingle (Cop.cast_int_single si1 i)))
      | _ => Ret None
      end
    | Cop.cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
        match Cop.cast_float_int si2 f with
        | Some i => Ret (Some (Vint (Cop.cast_int_int sz2 si2 i)))
        | None => Ret None
        end
      | _ => Ret None
      end
    | Cop.cast_case_s2i sz2 si2 =>
      match v with
      | Vsingle f =>
        match Cop.cast_single_int si2 f with
        | Some i => Ret (Some (Vint (Cop.cast_int_int sz2 si2 i)))
        | None => Ret None
        end
      | _ => Ret None
      end
    | Cop.cast_case_l2l =>
      match v with
      | Vlong n => Ret (Some (Vlong n))
      | _ => Ret None
      end
    | Cop.cast_case_i2l si =>
      match v with
      | Vint n => Ret (Some (Vlong (Cop.cast_int_long si n)))
      | _ => Ret None
      end
    | Cop.cast_case_l2i sz si =>
      match v with
      | Vlong n =>
        Ret (Some (Vint (Cop.cast_int_int sz si (Int.repr (Int64.unsigned n)))))
      | _ => Ret None
      end
    | Cop.cast_case_l2f si1 =>
      match v with
      | Vlong i => Ret (Some (Vfloat (Cop.cast_long_float si1 i)))
      | _ => Ret None
      end
    | Cop.cast_case_l2s si1 =>
      match v with
      | Vlong i => Ret (Some (Vsingle (Cop.cast_long_single si1 i)))
      | _ => Ret None
      end
    | Cop.cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
        match Cop.cast_float_long si2 f with
        | Some i => Ret (Some (Vlong i))
        | None => Ret None
        end
      | _ => Ret None
      end
    | Cop.cast_case_s2l si2 =>
      match v with
      | Vsingle f =>
        match Cop.cast_single_long si2 f with
        | Some i => Ret (Some (Vlong i))
        | None => Ret None
        end
      | _ => Ret None
      end
    | Cop.cast_case_i2bool =>
      match v with
      | Vint n => Ret (Some (Vint (if Int.eq n Int.zero then Int.zero else Int.one)))
      | Vptr b ofs =>
        if Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b (Ptrofs.unsigned ofs);;
          if (ret: bool)
          then Ret (Some Vone)
          else Ret None
      | _ => Ret None
      end
    | Cop.cast_case_l2bool =>
      match v with
      | Vlong n =>
        Ret (Some (Vint (if Int64.eq n Int64.zero then Int.zero else Int.one)))
      | Vptr b ofs =>
        if negb Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b (Ptrofs.unsigned ofs);;
          if (ret: bool)
          then Ret (Some Vone)
          else Ret None
      | _ => Ret None
      end
    | Cop.cast_case_f2bool =>
      match v with
      | Vfloat f =>
        Ret (Some
               (Vint
                  (if Floats.Float.cmp Ceq f Floats.Float.zero
                   then Int.zero
                   else Int.one)))
      | _ => Ret None
      end
    | Cop.cast_case_s2bool =>
      match v with
      | Vsingle f =>
        Ret (Some
               (Vint
                  (if Floats.Float32.cmp Ceq f Floats.Float32.zero
                   then Int.zero
                   else Int.one)))
      | _ => Ret None
      end
    | Cop.cast_case_struct id1 id2 | Cop.cast_case_union id1 id2 =>
                                     match v with
                                     | Vptr _ _ => if ident_eq id1 id2
                                                   then Ret (Some v) else Ret None
                                     | _ => Ret None
                                     end
    | Cop.cast_case_void => Ret (Some v)
    | Cop.cast_case_default => Ret None
    end.

  Definition sem_binarith_c sem_int sem_long sem_float sem_single
             v1 t1 v2 t2: itree eff (option val) :=
    let c := Cop.classify_binarith t1 t2 in
    let t := Cop.binarith_type c in
    v1' <- sem_cast_c v1 t1 t;;
    match v1' with
    | Some v1' =>
      v2' <- sem_cast_c v2 t2 t;;
      match v2' with
      | Some v2' =>
        match c with
        | Cop.bin_case_i sg =>
          match v1' with
          | Vint n1 =>
            match v2' with
            | Vint n2 => Ret (sem_int sg n1 n2)
            | _ => Ret None
            end
          | _ => Ret None
          end
        | Cop.bin_case_l sg =>
          match v1' with
          | Vlong n1 =>
            match v2' with
            | Vlong n2 => Ret (sem_long sg n1 n2)
            | _ => Ret None
            end
          | _ => Ret None
          end
        | Cop.bin_case_f =>
          match v1' with
          | Vfloat n1 =>
            match v2' with
            | Vfloat n2 => Ret (sem_float n1 n2)
            | _ => Ret None
            end
          | _ => Ret None
          end
        | Cop.bin_case_s =>
          match v1' with
          | Vsingle n1 =>
            match v2' with
            | Vsingle n2 => Ret (sem_single n1 n2)
            | _ => Ret None
            end
          | _ => Ret None
          end
        | Cop.bin_default => Ret None
        end
      | None => Ret None
      end
    | None => Ret None
    end.

  Definition sem_add_c cenv v1 t1 v2 t2: itree eff (option val) :=
    match Cop.classify_add t1 t2 with
    | Cop.add_case_pi ty si => Ret (Cop.sem_add_ptr_int cenv ty si v1 v2)
    | Cop.add_case_pl ty => Ret (Cop.sem_add_ptr_long cenv ty v1 v2)
    | Cop.add_case_ip si ty => Ret (Cop.sem_add_ptr_int cenv ty si v2 v1)
    | Cop.add_case_lp ty => Ret (Cop.sem_add_ptr_long cenv ty v2 v1)
    | Cop.add_default =>
      sem_binarith_c
        (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.add n1 n2)))
        (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.add n1 n2)))
        (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.add n1 n2)))
        (fun n1 n2 : Floats.float32 =>
           Some (Vsingle (Floats.Float32.add n1 n2))) v1 t1 v2 t2
    end.

  Definition sem_sub_c cenv v1 t1 v2 t2: itree eff (option val) :=
    match Cop.classify_sub t1 t2 with
    | Cop.sub_case_pi ty si =>
      match v1 with
      | Vint n1 =>
        match v2 with
        | Vint n2 =>
          if Archi.ptr64
          then Ret None
          else
            Ret (Some
                   (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2))))
        | _ => Ret None
        end
      | Vlong n1 =>
        match v2 with
        | Vint n2 =>
          let n3 := Cop.cast_int_long si n2 in
          if Archi.ptr64
          then
            Ret (Some
                   (Vlong
                      (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n3))))
          else Ret None
        | _ => Ret None
        end
      | Vptr b1 ofs1 =>
        match v2 with
        | Vint n2 =>
          let n3 := Cop.ptrofs_of_int si n2 in
          Ret (Some
                 (Vptr b1
                       (Ptrofs.sub ofs1
                                   (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3))))
        | _ => Ret None
        end
      | _ => Ret None
      end
    | Cop.sub_case_pp ty =>
      match v1 with
      | Vptr b1 ofs1 =>
        match v2 with
        | Vptr b2 ofs2 =>
          if eq_block b1 b2
          then
            let sz := sizeof cenv ty in
            if
              Coqlib.proj_sumbool (Coqlib.zlt 0 sz) &&
              Coqlib.proj_sumbool (Coqlib.zle sz Ptrofs.max_signed)
            then
              Ret (Some
                     (Vptrofs
                        (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz))))
            else Ret None
          else Ret None
        | _ => Ret None
        end
      | _ => Ret None
      end
    | Cop.sub_case_pl ty =>
      match v1 with
      | Vint n1 =>
        match v2 with
        | Vlong n2 =>
          let n3 := Int.repr (Int64.unsigned n2) in
          if Archi.ptr64
          then Ret None
          else
            Ret (Some
                   (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n3))))
        | _ => Ret None
        end
      | Vlong n1 =>
        match v2 with
        | Vlong n2 =>
          if Archi.ptr64
          then
            Ret (Some
                   (Vlong
                      (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))))
          else Ret None
        | _ => Ret None
        end
      | Vptr b1 ofs1 =>
        match v2 with
        | Vlong n2 =>
          let n3 := Ptrofs.of_int64 n2 in
          Ret (Some
                 (Vptr b1
                       (Ptrofs.sub ofs1
                                   (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3))))
        | _ => Ret None
        end
      | _ => Ret None
      end
    | Cop.sub_default =>
      sem_binarith_c
        (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.sub n1 n2)))
        (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.sub n1 n2)))
        (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.sub n1 n2)))
        (fun n1 n2 : Floats.float32 =>
           Some (Vsingle (Floats.Float32.sub n1 n2))) v1 t1 v2 t2
    end.

  Definition sem_mul_c v1 t1 v2 t2: itree eff (option val) :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.mul n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.mul n1 n2)))
      (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.mul n1 n2)))
      (fun n1 n2 : Floats.float32 => Some (Vsingle (Floats.Float32.mul n1 n2)))
      v1 t1 v2 t2.

  Definition sem_div_c v1 t1 v2 t2: itree eff (option val) :=
    sem_binarith_c
      (fun (sg : signedness) (n1 n2 : int) =>
         match sg with
         | Signed =>
           if
             Int.eq n2 Int.zero
             || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
           then None
           else Some (Vint (Int.divs n1 n2))
         | Unsigned =>
           if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
         end)
      (fun (sg : signedness) (n1 n2 : int64) =>
         match sg with
         | Signed =>
           if
             Int64.eq n2 Int64.zero
             || Int64.eq n1 (Int64.repr Int64.min_signed) &&
               Int64.eq n2 Int64.mone
           then None
           else Some (Vlong (Int64.divs n1 n2))
         | Unsigned =>
           if Int64.eq n2 Int64.zero
           then None
           else Some (Vlong (Int64.divu n1 n2))
         end) (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.div n1 n2)))
      (fun n1 n2 : Floats.float32 => Some (Vsingle (Floats.Float32.div n1 n2)))
      v1 t1 v2 t2.

  Definition sem_mod_c v1 t1 v2 t2: itree eff (option val) :=
    sem_binarith_c
      (fun (sg : signedness) (n1 n2 : int) =>
         match sg with
         | Signed =>
           if
             Int.eq n2 Int.zero
             || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
           then None
           else Some (Vint (Int.mods n1 n2))
         | Unsigned =>
           if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
         end)
      (fun (sg : signedness) (n1 n2 : int64) =>
         match sg with
         | Signed =>
           if
             Int64.eq n2 Int64.zero
             || Int64.eq n1 (Int64.repr Int64.min_signed) &&
               Int64.eq n2 Int64.mone
           then None
           else Some (Vlong (Int64.mods n1 n2))
         | Unsigned =>
           if Int64.eq n2 Int64.zero
           then None
           else Some (Vlong (Int64.modu n1 n2))
         end) (fun _ _ : Floats.float => None) (fun _ _ : Floats.float32 => None)
      v1 t1 v2 t2.
  
  Definition sem_and_c v1 t1 v2 t2: itree eff (option val) :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.and n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.and n1 n2)))
      (fun _ _ : Floats.float => None) (fun _ _ : Floats.float32 => None)
      v1 t1 v2 t2.

  Definition sem_or_c v1 t1 v2 t2: itree eff (option val) :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.or n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.or n1 n2)))
      (fun _ _ : Floats.float => None) (fun _ _ : Floats.float32 => None)
      v1 t1 v2 t2.

  Definition sem_xor_c v1 t1 v2 t2: itree eff (option val) :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.xor n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.xor n1 n2)))
      (fun _ _ : Floats.float => None) (fun _ _ : Floats.float32 => None)
      v1 t1 v2 t2.

  Definition cmplu_bool_c c v1 v2 : itree eff (option bool) :=
    match v1 with
    | Vlong n1 =>
      match v2 with
      | Vlong n2 => Ret (Some (Int64.cmpu c n1 n2))
      | Vptr b2 ofs2 =>
        if negb Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b2 (Ptrofs.unsigned ofs2);;
          if
            Int64.eq n1 Int64.zero && ret
          then Ret (Val.cmp_different_blocks c)
          else Ret None
      | _ => Ret None
      end
    | Vptr b1 ofs1 =>
      match v2 with
      | Vlong n2 =>
        if negb Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b1 (Ptrofs.unsigned ofs1);;
          if
            Int64.eq n2 Int64.zero && ret
          then Ret (Val.cmp_different_blocks c)
          else Ret None
      | Vptr b2 ofs2 =>
        if negb Archi.ptr64
        then Ret None
        else
          if eq_block b1 b2
          then
            ret1 <- weak_valid_pointer_c b1 (Ptrofs.unsigned ofs1);;
            ret2 <- weak_valid_pointer_c b2 (Ptrofs.unsigned ofs2);;
            if
              ret1 && ret2
            then Ret (Some (Ptrofs.cmpu c ofs1 ofs2))
            else Ret None
          else
            ret1 <- ccallU "valid_pointer" (b1, ofs1);;
            ret2 <- ccallU "valid_pointer" (b2, ofs2);;
            if
              ret1 && ret2
            then Ret (Val.cmp_different_blocks c)
            else Ret None
      | _ => Ret None
      end
    | _ => Ret None
    end.

  Definition cmpu_bool_c c v1 v2 : itree eff (option bool) :=
    match v1 with
    | Vint n1 =>
      match v2 with
      | Vint n2 => Ret (Some (Int.cmpu c n1 n2))
      | Vptr b2 ofs2 =>
        if negb Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b2 (Ptrofs.unsigned ofs2);;
          if
            Int.eq n1 Int.zero && ret
          then Ret (Val.cmp_different_blocks c)
          else Ret None
      | _ => Ret None
      end
    | Vptr b1 ofs1 =>
      match v2 with
      | Vint n2 =>
        if negb Archi.ptr64
        then Ret None
        else
          ret <- weak_valid_pointer_c b1 (Ptrofs.unsigned ofs1);;
          if
            Int.eq n2 Int.zero && ret
          then Ret (Val.cmp_different_blocks c)
          else Ret None
      | Vptr b2 ofs2 =>
        if Archi.ptr64
        then Ret None
        else
          if eq_block b1 b2
          then
            ret1 <- weak_valid_pointer_c b1 (Ptrofs.unsigned ofs1);;
            ret2 <- weak_valid_pointer_c b2 (Ptrofs.unsigned ofs2);;
            if
              ret1 && ret2
            then Ret (Some (Ptrofs.cmpu c ofs1 ofs2))
            else Ret None
          else
            ret1 <- ccallU "valid_pointer" (b1, ofs1);;
            ret2 <- ccallU "valid_pointer" (b2, ofs2);;
            if
              ret1 && ret2
            then Ret (Val.cmp_different_blocks c)
            else Ret None
      | _ => Ret None
      end
    | _ => Ret None
    end.

  Definition cmp_ptr_c c v1 v2: itree eff (option val) :=
    ret <- (if Archi.ptr64
            then cmplu_bool_c c v1 v2
            else cmpu_bool_c c v1 v2);;
    Ret (Coqlib.option_map Val.of_bool ret).
  
  Definition sem_cmp_c c v1 t1 v2 t2: itree eff (option val) :=
    match Cop.classify_cmp t1 t2 with
    | Cop.cmp_case_pp => cmp_ptr_c c v1 v2
    | Cop.cmp_case_pi si =>
      match v2 with
      | Vint n2 =>
        let v2' := Vptrofs (Cop.ptrofs_of_int si n2) in
        cmp_ptr_c c v1 v2'
      | Vptr _ _ => if Archi.ptr64 then Ret None else cmp_ptr_c  c v1 v2
      | _ => Ret None
      end
    | Cop.cmp_case_ip si =>
      match v1 with
      | Vint n1 =>
        let v1' := Vptrofs (Cop.ptrofs_of_int si n1) in
        cmp_ptr_c c v1' v2
      | Vptr _ _ => if Archi.ptr64 then Ret None else cmp_ptr_c c v1 v2
      | _ => Ret None
      end
    | Cop.cmp_case_pl =>
      match v2 with
      | Vlong n2 =>
        let v2' := Vptrofs (Ptrofs.of_int64 n2) in cmp_ptr_c c v1 v2'
      | Vptr _ _ => if Archi.ptr64 then cmp_ptr_c c v1 v2 else Ret None
      | _ => Ret None
      end
    | Cop.cmp_case_lp =>
      match v1 with
      | Vlong n1 =>
        let v1' := Vptrofs (Ptrofs.of_int64 n1) in cmp_ptr_c c v1' v2
      | Vptr _ _ => if Archi.ptr64 then cmp_ptr_c c v1 v2 else Ret None
      | _ => Ret None
      end
    | Cop.cmp_default =>
      sem_binarith_c
        (fun (sg : signedness) (n1 n2 : int) =>
           Some
             (Val.of_bool
                match sg with
                | Signed => Int.cmp c n1 n2
                | Unsigned => Int.cmpu c n1 n2
                end))
        (fun (sg : signedness) (n1 n2 : int64) =>
           Some
             (Val.of_bool
                match sg with
                | Signed => Int64.cmp c n1 n2
                | Unsigned => Int64.cmpu c n1 n2
                end))
        (fun n1 n2 : Floats.float =>
           Some (Val.of_bool (Floats.Float.cmp c n1 n2)))
        (fun n1 n2 : Floats.float32 =>
           Some (Val.of_bool (Floats.Float32.cmp c n1 n2))) v1 t1 v2 t2
    end.

  Definition binary_op_c cenv op v1 t1 v2 t2: itree eff (option val) :=
    match op with
    | Cop.Oadd => sem_add_c cenv v1 t1 v2 t2
    | Cop.Osub => sem_sub_c cenv v1 t1 v2 t2
    | Cop.Omul => sem_mul_c v1 t1 v2 t2
    | Cop.Odiv => sem_div_c v1 t1 v2 t2
    | Cop.Omod => sem_mod_c v1 t1 v2 t2
    | Cop.Oand => sem_and_c v1 t1 v2 t2
    | Cop.Oor => sem_or_c v1 t1 v2 t2
    | Cop.Oxor => sem_xor_c v1 t1 v2 t2
    | Cop.Oshl => Ret (Cop.sem_shl v1 t1 v2 t2)
    | Cop.Oshr => Ret (Cop.sem_shr v1 t1 v2 t2)
    | Cop.Oeq => sem_cmp_c Ceq v1 t1 v2 t2
    | Cop.One => sem_cmp_c Cne v1 t1 v2 t2
    | Cop.Olt => sem_cmp_c Clt v1 t1 v2 t2
    | Cop.Ogt => sem_cmp_c Cgt v1 t1 v2 t2
    | Cop.Ole => sem_cmp_c Cle v1 t1 v2 t2
    | Cop.Oge => sem_cmp_c Cge v1 t1 v2 t2
    end.
  
  Fixpoint eval_expr_c (expr: Clight.expr): itree eff (option val) :=
    match expr with
    | Econst_int i ty => Ret (Some (Vint i))
    | Econst_float f ty => Ret (Some (Vfloat f))
    | Econst_single f ty => Ret (Some (Vsingle f))
    | Econst_long i ty => Ret (Some (Vlong i))
    | Etempvar id ty => Ret ((le ! id))
    | Eaddrof a ty =>
      v <- _eval_lvalue_c eval_expr_c a;;
      match v with
      | None => Ret None (*??*)
      | Some (loc, (ofs, bf)) => Ret (Some (Vptr loc ofs))
      end
    | Eunop op a ty =>
      v <- eval_expr_c a;;
      match v with
      | None => Ret None
      | Some v1 =>
        unary_op_c op v1 (Clight.typeof a)
      end
    | Ebinop op a1 a2 ty =>
      v1 <- eval_expr_c a1;;
      v2 <- eval_expr_c a2;;
      match v1, v2 with
      | Some v1, Some v2 =>
        binary_op_c ce op
                    v1 (Clight.typeof a1)
                    v2 (Clight.typeof a2)
      | _, _ => Ret None
      end
    | Ecast a ty =>
      v <- eval_expr_c a;;
      match v with
      | None => Ret None
      | Some v1 =>
        sem_cast_c v1 (Clight.typeof a) ty
      end
    | Esizeof ty1 ty =>
      Ret (Some (Vptrofs (Ptrofs.repr (sizeof ce ty1))))
    | Ealignof ty1 ty =>
      Ret (Some (Vptrofs (Ptrofs.repr (alignof ce ty1))))
    | a =>
      v <- _eval_lvalue_c eval_expr_c a;;
      match v with
      | None => Ret None
      | Some (loc, (ofs, bf)) =>
        v <- deref_loc_c (Clight.typeof a) loc ofs;; Ret v
      end
    end.


  Definition eval_lvalue_c
    : expr -> itree eff (option (block * (ptrofs * bitfield))) :=
    _eval_lvalue_c eval_expr_c.

  Fixpoint eval_exprlist_c
           (es: list expr) (ts: typelist)
    : itree eff (option (list val)) :=
    match es, ts with
    | [], Ctypes.Tnil =>
        Ret (Some [])
    | e::es', Ctypes.Tcons ty ts' =>
      v1 <- eval_expr_c e;;
      vs <- eval_exprlist_c es' ts';; 
      match v1, vs with
      | Some v1, Some vs =>
        v2 <- sem_cast_c v1 (typeof e) ty;;
        match v2 with
        | Some v2 => Ret (Some (v2::vs))
        | None => Ret None
        end
      | _, _ =>
          Ret None
      end
    | _, _ => Ret None
    end.

End EVAL_EXPR_COMP.

Definition id_list_norepet_c: list ident -> bool :=
  fun ids => if Coqlib.list_norepet_dec (ident_eq) ids then true else false.

Definition id_list_disjoint_c: list ident -> list ident -> bool :=
  fun ids1 ids2 =>
    if (Coqlib.list_disjoint_dec ident_eq ids1 ids2)
    then true else false.

Fixpoint alloc_variables_c (ce: composite_env) (e: env)
         (vars: list (ident * type))
  : itree eff env := 
  match vars with
  | [] => Ret e
  | (id, ty) :: vars' =>
    v <- ccallU "salloc" (0%Z, sizeof ce ty);;
    match v with
    | Vptr b ofs => alloc_variables_c ce (PTree.set id (b, ty) e) vars'
    | _ => triggerUB
    end
  end.

Definition function_entry_c
           (ce: composite_env) (f: function) (vargs: list val)
  : itree eff (option (env * temp_env)) :=
  if (id_list_norepet_c (var_names (fn_vars f)) &&
      id_list_norepet_c (var_names (fn_params f)) &&
      id_list_disjoint_c (var_names (fn_params f))
                         (var_names (fn_temps f)))%bool
  then
    e <- alloc_variables_c ce empty_env (fn_vars f);;
    match
      bind_parameter_temps (fn_params f) vargs
                            (create_undef_temps
                               (fn_temps f))
    with
    | None => Ret None
    | Some le => Ret

 (Some (e, le))
    end
  else Ret None.

Section DECOMP.

  Definition runtime_env : Type := env * temp_env * option bool * option val.

  Notation itr_t := (itree eff runtime_env).

  Definition _sassign_c e le a1 a2 :=
    v <- eval_lvalue_c e le a1;;
    match v with
    | Some (loc, (ofs, bf)) =>
      v2 <- eval_expr_c e le a2;; 
      match v2 with
      | Some v2 =>
        v <- sem_cast_c v2 (typeof a2) (typeof a1);;
        match v with
        | Some v =>
          assign_loc_c ce (typeof a1) loc ofs v
        | None => Ret tt
        end
      | None => Ret tt
      end
    | None => Ret tt
    end.

  Definition _scall_c e le a al
    : itree eff val :=
    match Cop.classify_fun (typeof a) with
    | Cop.fun_case_f tyargs tyres cconv =>
      vf <- (eval_expr_c e le a);;
      vf <- vf?;;
      vargs <- eval_exprlist_c e le al tyargs;;
      vargs <- vargs?;;
      match vf with
      | Vptr b ofs =>
          '(gsym, skentry) <- (nth_error sk (pred (Pos.to_nat b)))?;;
          gd <- (skentry↓)?;;
          fd <- (match gd with Cgfun fd => Some fd | _ => None end)?;;
          if type_eq fd
               (Tfunction tyargs tyres cconv)
          then ccallU gsym vargs
          else triggerUB
      | _ => triggerUB (* unreachable b*)
      end
    | _ => triggerUB
    end.

  Definition _site_c
             (e: env) (le: temp_env) (a: expr)
    : itree eff (option bool) :=
    v1 <- eval_expr_c e le a;;
    match v1 with
    | Some v1 =>
      bool_val_c v1 (typeof a)
    | None => Ret None
    end.

  Definition sloop_iter_body_one
             (itr: itr_t)
    : itree eff (env * temp_env * (option (option val))) :=
    '(e', le', obc, v) <- itr;;
    match v with
    | Some retv =>
      (* return *)
      Ret (e', le', Some (Some retv))
    | None =>
      if (* is_break *)
        match obc with
        | None => false
        | Some bc => bc
        end
      then
        (* break, not return *)
        Ret (e', le', Some None)
      else
        (* continue *)
        Ret (e', le', None)
    end.

  Definition sloop_iter_body_two
             (itr: itr_t)
    : itree eff (env * temp_env * (option (option val))) :=
    '(e', le', obc, v) <- itr;;
    match v with
    | Some retv =>
      (* return *)
      Ret (e', le', Some (Some retv))
    | None =>
      match obc with
      | Some true => Ret (e', le', Some None)
      | Some false => triggerUB
      | None => Ret (e', le', None)
      end
    end.

  Definition sloop_iter_body
             (itr1 itr2: env -> temp_env -> itr_t)
             (i: env * temp_env)
    : itree eff
            (env * temp_env +
             env * temp_env * option val) :=
    let '(e, le) := i in
    (* '(e1, le1, m1, obc1, v1) <- itr1 e le m ;; *)
    '(e1, le1, ov1) <- sloop_iter_body_one (itr1 e le) ;;
    match ov1 with
    | Some v1 =>
      (* break or return *)
      Ret (inr (e1, le1, v1))
    | None =>
      (* run loop2 *)
      '(e2, le2, ov2) <- sloop_iter_body_two (itr2 e1 le1);;
      match ov2 with
      | Some v2 =>
        Ret (inr (e2, le2, v2))
      | None =>
        Ret (inl (e2, le2))
      end
    end.

  Definition _sloop_itree
             (e: env) (le: temp_env)
             (itr1 itr2: env -> temp_env -> itr_t)
    : itr_t :=
    '(e', le', v) <-
    ITree.iter (sloop_iter_body itr1 itr2) (e, le) ;;
    Ret (e', le', None, v).

  Fixpoint free_list_aux (l: list (block * Z * Z)): itree eff unit :=
    match l with
    | nil => Ret tt
    | (b, lo, hi):: l' =>
      @ccallU _ _ _ _ unit "sfree" (b, lo, hi);;;
      free_list_aux l'
    end.

  Definition block_of_binding (ce: composite_env) (id_b_ty: ident * (block * type)) :=
    let (_, p) := id_b_ty in let (b, ty) := p in (b, 0%Z, sizeof ce ty).

  Definition blocks_of_env (ce: composite_env) :=
    List.map (block_of_binding ce) ∘ PTree.elements.
  
  Definition _sreturn_c
             (retty: type)
             (e: env) (le: temp_env)
             (oa: option expr)
    : itree eff (option val) :=
    match oa with
    | None => Ret (Some Vundef)
    | Some a =>
      v <- eval_expr_c e le a;;
      match v with
      | None => Ret None
      | Some v =>
        sem_cast_c v (typeof a) retty
      end
    end.

  Fixpoint decomp_stmt
           (retty: type)
           (stmt: statement) (* (k: cont) *)
           (e: env) (le: temp_env)
    : itr_t :=
    match stmt with
    | Sskip =>
      tau;;Ret ((* k, *) e, le, None, None)
    | Sassign a1 a2 =>
      _sassign_c e le a1 a2;;;
      Ret (e, le, None, None)
    | Sset id a =>
      v <- eval_expr_c e le a ;;
      match v with
      | Some v =>
        let le' := PTree.set id v le in
        Ret (e, le', None, None)
      | None =>
        triggerUB
      end
    | Scall optid a al =>
        v <- _scall_c e le a al;;
        Ret (e, (set_opttemp optid v le), None, None)
    | Sbuiltin optid ef targs el => triggerUB
    | Ssequence s1 s2 =>
      '(e', le', bc, v) <- decomp_stmt retty s1 e le;;
      match v with
      | Some retval =>
        Ret (e', le', None, v)
      | None =>
        match bc with
        | None =>
          decomp_stmt retty s2 e' le'
        | Some _ =>
          Ret (e', le', bc, None)
        end
      end
    | Sifthenelse a s1 s2 =>
      b <- _site_c e le a;;
      match b with
      | Some b =>
        if (b: bool) then (decomp_stmt retty s1 e le)
        else (decomp_stmt retty s2 e le)
      | None =>
        triggerUB
      end
    | Sloop s1 s2 =>
      let itr1 := decomp_stmt retty s1 in
      let itr2 := decomp_stmt retty s2 in
      _sloop_itree e le itr1 itr2
    (* '(e, le, m, bc, v) <- itr ;; *)

    | Sbreak =>
      Ret (e, le, Some true, None)
    | Scontinue =>
      Ret (e, le, Some false, None)
    | Sreturn oa =>
      v <- _sreturn_c retty e le oa;;
      match v with
      | Some v =>
        Ret (e, le, None, Some v)
      | None =>
        triggerUB
      end
    | _ =>
      (* not supported *)
      triggerUB
    end.

  Definition decomp_func
           (f: Clight.function)
           (vargs: list val)
    : itree eff val :=
    t <- function_entry_c ce f vargs;;
    match t with
    | None => triggerUB
    | Some (e, le) =>
      '(e', _, c, ov) <- decomp_stmt (fn_return f) (fn_body f) e le;; c?;;;
      free_list_aux (blocks_of_env ce e');;;
      let v := match ov with
               | None => Vundef
               | Some v => v
               end
      in
      Ret v
    end.

    Lemma unfold_decomp_stmt :
    decomp_stmt =
  fun retty stmt e le =>
    match stmt with
    | Sskip =>
      tau;;Ret ((* k, *) e, le, None, None)
    | Sassign a1 a2 =>
      _sassign_c e le a1 a2;;;
      Ret (e, le, None, None)
    | Sset id a =>
      v <- eval_expr_c e le a ;;
      match v with
      | Some v =>
        let le' := PTree.set id v le in
        Ret (e, le', None, None)
      | None =>
        triggerUB
      end
    | Scall optid a al =>
        v <- _scall_c e le a al;;
        Ret (e, (set_opttemp optid v le), None, None)
    | Sbuiltin optid ef targs el => triggerUB
    | Ssequence s1 s2 =>
      '(e', le', bc, v) <- decomp_stmt retty s1 e le;;
      match v with
      | Some retval =>
        Ret (e', le', None, v)
      | None =>
        match bc with
        | None =>
          decomp_stmt retty s2 e' le'
        | Some _ =>
          Ret (e', le', bc, None)
        end
      end
    | Sifthenelse a s1 s2 =>
      b <- _site_c e le a;;
      match b with
      | Some b =>
        if (b: bool) then (decomp_stmt retty s1 e le)
        else (decomp_stmt retty s2 e le)
      | None =>
        triggerUB
      end
    | Sloop s1 s2 =>
      let itr1 := decomp_stmt retty s1 in
      let itr2 := decomp_stmt retty s2 in
      _sloop_itree e le itr1 itr2
    (* '(e, le, m, bc, v) <- itr ;; *)

    | Sbreak =>
      Ret (e, le, Some true, None)
    | Scontinue =>
      Ret (e, le, Some false, None)
    | Sreturn oa =>
      v <- _sreturn_c retty e le oa;;
      match v with
      | Some v =>
        Ret (e, le, None, Some v)
      | None =>
        triggerUB
      end
    | _ =>
      (* not supported *)
      triggerUB
    end.
    Proof. repeat (apply func_ext; i). destruct x0; et. Qed.

End DECOMP.
End Clight.
(* Notation call_data := (block * (* fundef * *) list val * mem)%type. *)

(* Section TRANS. *)

(*   (* Variable cprog_app: Clight.program. *) *)
(*   Variable global_definitions : list (ident * globdef fundef type). *)
(*   Variable public_idents : list ident. *)
(*   Let defined_names := List.map fst global_definitions. *)

(*   Fixpoint filter_dec_not {A: Type} {P: A -> Prop} (f: forall x: A, {P x} + {~ P x}) (l: list A) : list A := *)
(*     match l with *)
(*     | nil => nil *)
(*     | x :: l' => if f x then filter_dec_not f l' else x :: (filter_dec_not f l') *)
(*     end. *)
  
(*   Definition in_public x := in_dec Pos.eq_dec x public_idents. *)
  
(*   Definition rest_names := filter_dec_not in_public defined_names. *)

(*   Definition in_rest x := in_dec Pos.eq_dec x rest_names. *)

(*   Variable src_name : string.   (* source code file name *) *)

(*   Definition prefix_pos pos := ident_of_string (src_name ++ "." ++ (string_of_ident pos))%string. *)

(*   Definition rpl_pos pos := if in_rest pos then prefix_pos pos else pos. *)

(*   Definition rpl_glob := List.map (fun x => (rpl_pos (fst x), snd x)) global_definitions. *)
  
(*   Fixpoint rpl_expr (e: expr) := *)
(*     match e with *)
(*     | Econst_int _ _ | Econst_float _ _ | Econst_single _ _ *)
(*     | Econst_long _ _ | Etempvar _ _ | Esizeof _ _ | Ealignof _ _ => e *)
(*     | Evar id ty => Evar (rpl_pos id) ty *)
(*     | Ederef e' ty => Ederef (rpl_expr e') ty *)
(*     | Eaddrof e' ty => Eaddrof (rpl_expr e') ty *)
(*     | Eunop uop e' ty => Eunop uop (rpl_expr e') ty *)
(*     | Ebinop bop e1 e2 ty => Ebinop bop (rpl_expr e1) (rpl_expr e2) ty *)
(*     | Ecast e' ty => Ecast (rpl_expr e') ty *)
(*     | Efield e' id ty => Efield (rpl_expr e') id ty *)
(*     end. *)
  
(*   Fixpoint rpl_body (s : statement) := *)
(*     match s with *)
(*     | Sskip | Sbreak | Scontinue | Sgoto _ => s *)
(*     | Sassign a1 a2 => Sassign (rpl_expr a1) (rpl_expr a2) *)
(*     | Sset id a => Sset (rpl_pos id) (rpl_expr a) *)
(*     | Scall optid a al => *)
(*         Scall *)
(*           (option_rec (fun _ => _) (Some ∘ rpl_pos) None optid) *)
(*           (rpl_expr a) (List.map rpl_expr al) *)
(*     | Sbuiltin optid ef targs el => *)
(*         Sbuiltin *)
(*           (option_rec (fun _ => _) (Some ∘ rpl_pos) None optid) *)
(*           ef targs (List.map rpl_expr el) *)
(*     | Ssequence s1 s2 => Ssequence (rpl_body s1) (rpl_body s2) *)
(*     | Sifthenelse a s1 s2 => Sifthenelse (rpl_expr a) (rpl_body s1) (rpl_body s2) *)
(*     | Sloop s1 s2 => Sloop (rpl_body s1) (rpl_body s2) *)
(*     | Sreturn oa => Sreturn (option_rec (fun _ => _) (Some ∘ (rpl_expr)) None oa) *)
(*     | Sswitch a ls => Sswitch (rpl_expr a) (rpl_labeled_stmt ls) *)
(*     | Slabel l s => Slabel l (rpl_body s) *)
(*     end *)
      
(*   with rpl_labeled_stmt (ls: labeled_statements) := *)
(*          match ls with *)
(*          | LSnil => LSnil *)
(*          | LScons optz s ls' => LScons optz (rpl_body s) (rpl_labeled_stmt ls') *)
(*          end. *)
  
(*   Definition trans_func (f: function) := *)
(*     mkfunction f.(fn_return) f.(fn_callconv) f.(fn_params) f.(fn_vars) f.(fn_temps) (rpl_body f.(fn_body)). *)

(*   Definition trans_initval (ii : init_data) := *)
(*     match ii with *)
(*     | Init_addrof id ofs => Init_addrof (rpl_pos id) ofs *)
(*     | _ => ii *)
(*     end. *)

(*   Definition trans_var (gv: globvar type) := *)
(*     {| *)
(*       gvar_info := gv.(gvar_info); *)
(*       gvar_init := List.map trans_initval gv.(gvar_init); *)
(*       gvar_readonly := gv.(gvar_readonly); *)
(*       gvar_volatile := gv.(gvar_volatile); *)
(*     |} *)
(*   . *)

(*   Definition trans_global_def (g_def: globdef fundef type) := *)
(*     match g_def with *)
(*     | Gvar gv => Gvar (trans_var gv) *)
(*     | Gfun (Internal f) => Gfun (Internal (trans_func f)) *)
(*     | _ => g_def *)
(*     end. *)


(*   Definition trans_global_defs (g_defs: list (ident * globdef fundef type)) := *)
(*     List.map (fun x => (rpl_pos (fst x), trans_global_def (snd x))) g_defs. *)

(*   (* Program Definition append_srcname : Clight.program :=  *) *)
(*   (*   {| *) *)
(*   (*     prog_defs := trans_global_defs global_definitions; *) *)
(*   (*     prog_public := public_idents; *) *)
(*   (*     prog_main := cprog_app.(prog_main); *) *)
(*   (*     prog_types := cprog_app.(prog_types); *) *)
(*   (*     prog_comp_env := cprog_app.(prog_comp_env); *) *)
(*   (*   |}. *) *)
(*   (* Next Obligation. destruct cprog_app;auto. Qed. *) *)

(* End TRANS. *)

(* Section SITE_APP. *)
(*   (* for site specific execution *) *)
(*   (* not for proof *) *)
(*   Import EventsL. *)

(*   Definition sname := string. *)
(*   Variable sn: sname. *)
(*   Variable shared_fun_list: list gname. *)

(*   Let is_shared_fun fn := in_dec string_dec fn shared_fun_list. *)

(*   Definition site_append_morph_1 : Es ~> Es. (* for site specific module *) *)
(*   Proof. *)
(*     intros. destruct X. *)
(*     { destruct c. destruct (is_shared_fun fn). *)
(*       - exact (inl1 (Call mn fn args)). *)
(*       - exact (inl1 (Call mn (sn ++ "." ++ fn) args)). } *)
(*     destruct s. *)
(*     { destruct s. *)
(*       { destruct (is_shared_fun fn). *)
(*         - exact (inr1 (inl1 (Spawn fn args))). *)
(*         - exact (inr1 (inl1 (Spawn (sn ++ "." ++ fn) args))). } *)
(*       exact (inr1 (inl1 Yield)). *)
(*       exact (inr1 (inl1 Getpid)). *)
(*       exact (inr1 (inl1 Getsn)). } *)
(*     destruct s. *)
(*     { destruct p. *)
(*       - exact (inr1 (inr1 (inl1 (PPut (sn ++ "." ++ mn) p)))). *)
(*       - exact (inr1 (inr1 (inl1 (PGet (sn ++ "." ++ mn))))). } *)
(*     { destruct e. *)
(*       exact (inr1 (inr1 (inr1 (Choose X)))). *)
(*       exact (inr1 (inr1 (inr1 (Take X)))). *)
(*       exact (inr1 (inr1 (inr1 (Syscall fn args rvs)))). } *)
(*   Defined. *)
  
(*   Definition site_append_morph_2 (sn': sname) : Es ~> Es. (* for shared module *) *)
(*   Proof. *)
(*     intros. destruct X. *)
(*     { destruct c. destruct (is_shared_fun fn). *)
(*       - exact (inl1 (Call mn fn args)). *)
(*       - exact (inl1 (Call mn (sn' ++ "." ++ fn) args)). } *)
(*     destruct s. *)
(*     { destruct s. *)
(*       { destruct (is_shared_fun fn). *)
(*         - exact (inr1 (inl1 (Spawn fn args))). *)
(*         - exact (inr1 (inl1 (Spawn (sn' ++ "." ++ fn) args))). } *)
(*       exact (inr1 (inl1 Yield)). *)
(*       exact (inr1 (inl1 Getpid)). *)
(*       exact (inr1 (inl1 Getsn)). *)
(*     } *)
(*     destruct s. *)
(*     { destruct p. *)
(*       - exact (inr1 (inr1 (inl1 (PPut mn p)))). *)
(*       - exact (inr1 (inr1 (inl1 (PGet mn)))). } *)
(*     { destruct e. *)
(*       exact (inr1 (inr1 (inr1 (Choose X)))). *)
(*       exact (inr1 (inr1 (inr1 (Take X)))). *)
(*       exact (inr1 (inr1 (inr1 (Syscall fn args rvs)))). } *)
(*   Defined. *)
    

(*   Definition site_appended_itree_1 : itree Es ~> itree Es := translate site_append_morph_1. *)
(*   Definition site_appended_itree_2 (sn': sname) : itree Es ~> itree Es := translate (site_append_morph_2 sn'). *)

(*   Definition append_site_1 (ms: ModSemL.t) : ModSemL.t := *)
(*     {| *)
(*       ModSemL.fnsems := List.map (fun '(gn, fnsem) => *)
(*                        ((sn ++ "." ++ gn)%string, fun x => site_appended_itree_1 _ (fnsem x))) ms.(ModSemL.fnsems); *)
(*       ModSemL.initial_mrs := List.map (map_fst (fun mn => (sn ++ "." ++ mn)%string)) ms.(ModSemL.initial_mrs); *)
(*     |} *)
(*   . *)

(*   Definition append_caller_site {X Y: Type} (body: X -> itree Es Y) := *)
(*     fun x => sn' <- trigger Getsn;; site_appended_itree_2 sn' _ (body x). *)

(*   Definition append_site_2 (ms: ModSemL.t) : ModSemL.t := *)
(*     {| *)
(*       ModSemL.fnsems := List.map *)
(*                           (fun '(gn, fnsem) => (gn, append_caller_site fnsem)) ms.(ModSemL.fnsems); *)
(*       ModSemL.initial_mrs := ms.(ModSemL.initial_mrs); *)
(*     |} *)
(*   . *)

(* End SITE_APP. *)


Section DECOMP_PROG.

  (* Context `{SystemEnv}. *)
  Variable types: list composite_definition.
  Variable defs: list (ident * globdef Clight.fundef type).
  Variable public: list ident.
  Variable wf: wf_composites types.
  Let ce: composite_env := let (ce, _) := build_composite_env' types wf in ce.
  
  Variable mn: string.

  (* Fixpoint get_source_name (filename : string) := *)
  (*   String.substring 0 (String.length filename - 2) filename. *)

  Fixpoint decomp_fundefs (sk: Sk.t)
           (defs: list (ident * globdef Clight.fundef type))
    : list (ident * (list val -> itree Es val)) :=
    match defs with
    | [] => []
    | (id, gdef) :: defs' =>
      match gdef with
      | Gvar _ => decomp_fundefs sk defs'
      | Gfun fd =>
        match fd with
        | Internal f => 
          (id, fun vl => 
                  v <- decomp_func sk ce f vl;; 
                  (if Pos.eq_dec id (ident_of_string "main")
                   then (match v with Vint _ => Ret v | _ => triggerUB end)
                   else Ret v)) :: decomp_fundefs sk defs'
        | _ => decomp_fundefs sk defs'
        end
      end
    end.

  Fixpoint get_sk (defs: list (ident * globdef Clight.fundef type)) :=
    match defs with
    | [] => []
    | (id, gdef) :: defs' =>
        match gdef with
        | Gvar gv =>
            match gv.(gvar_init) with
            | [] => get_sk defs'
            | _ => (string_of_ident id, (Cgvar gv)↑) :: get_sk defs'
            end
        | Gfun gf =>
            match gf with
            | Internal f => (string_of_ident id, (Cgfun (type_of_function f))↑) :: get_sk defs'
            | _ => get_sk defs'
            end
        end
    end
  .

  Definition modsem (sk: Sk.t) : ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, f) => (string_of_ident fn, cfunU f)) (decomp_fundefs sk defs);
    ModSem.mn := mn;
    ModSem.initial_st := tt↑;
  |}.

  Definition get_mod : Mod.t := {|
    Mod.get_modsem := modsem;
    Mod.sk := get_sk defs;
  |}.

End DECOMP_PROG.

(* Section EXECUTION_STRUCTURE. *)
(*   (*   execution modules consist of modules executes in sites independently  *) *)
(*   (*   and modules accessable in every sites. *) *)
(*   (* ------------------------------------------------------------------------ *) *)
(*   (* example *) *)
(*   (* site A : A1 A2 A3 *) *)
(*   (* site B : B1 B2 B3 *) *)
(*   (* shared : C1 C2 C3 *) *)
(*   (* f: function append site name in local state and its own function *) *)
(*   (* g: function append current site name in site specific function (so, its site name dynamically determined) *) *)
(*   (* A's ModSemL: f (MemA + A1 + A2 + A3) <_ (enclose) skel of site A and shared *) *)
(*   (* B's ModSemL: f (MemB + B1 + B2 + B3) <_ (enclose) skel of site B and shared *) *)
(*   (* shared's ModSemL: g (C1 + C2 + C3) <_(enclose) skel of site A and site B and shared *) *)

(*   Fixpoint remove_mult_name (l : Sk.t) : Sk.t := *)
(*     match l with *)
(*       | [] => [] *)
(*       | (gn, gd)::xs => if in_dec string_dec gn (List.map fst xs) then remove_mult_name xs else (gn, gd)::(remove_mult_name xs) *)
(*     end. *)

(*   (* for skeleton padding *) *)
(*   Definition sk_padmod (sk: Sk.t) := ModL.mk ModL.empty.(ModL.get_modsem) sk. *)

(*   (* get one site's ModSemL *) *)
(*   Definition proc_gen (shared_module: ModL.t) : sname * list Mod.t -> ModSemL.t := *)
(*     fun '(sn, modlist) => *)
(*       (append_site_1 sn (List.map fst shared_module.(ModL.enclose).(ModSemL.fnsems)) *)
(*          (ModL.enclose (ModL.add (Mod.add_list modlist) (sk_padmod shared_module.(ModL.sk))))). *)
  
(*   (* turns exec_profile into one ModSemL *) *)
(*   Definition sum_of_site_modules_view (exec_profile: list (sname * list Mod.t)) (shared_module: ModL.t) : ModSemL.t := *)
(*     List.fold_left ModSemL.add (List.map (proc_gen shared_module) exec_profile) (ModSemL.mk [] []). *)

(*   (* get all skeletons in sites and concat *) *)
(*   Definition sum_of_site_skeletons (exec_profile: list (sname * list Mod.t)) : Sk.t := *)
(*       remove_mult_name (List.concat (List.map (fun '(sn, modlist) => (Mod.add_list modlist).(ModL.sk)) exec_profile)). *)

(*   (* turn shared modules into one ModSemL *) *)
(*   Definition view_shared_module (exec_profile: list (sname * list Mod.t)) (shared_module: ModL.t) : ModSemL.t := *)
(*     append_site_2 (List.map fst shared_module.(ModL.enclose).(ModSemL.fnsems)) *)
(*       (ModL.enclose (ModL.add shared_module (sk_padmod (sum_of_site_skeletons exec_profile)))). *)
  
(* End EXECUTION_STRUCTURE. *)
