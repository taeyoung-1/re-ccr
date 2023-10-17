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

(* Section GType.
  
  Inductive C_SkelEntry:=
  | Cgfun (function_type: type)
  | Cgvar (gv: globvar type)
  .

End GType. *)

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

  Definition load_bitfield_c (ty: type) 
            (sz: intsize) (sg: signedness) (pos: Z) (width: Z) 
            (addr: val) : itree eff val :=
  let chk := (0 <=? pos) && (0 <? width) 
            && (width <=? bitsize_intsize sz) 
            && (pos + width <=? Cop.bitsize_carrier sz) in
  match ty, chk with
  | Tint i sg1 attr, true =>
    if intsize_eq i sz then
      if signedness_eq sg1
          (if Coqlib.zlt width (bitsize_intsize sz) 
          then Signed else sg) 
      then v <- ccallU "load" (Cop.chunk_for_carrier sz, addr);;
        match v with
        | Vint c => 
          Ret (Vint (Cop.bitfield_extract sz sg pos width c))
        | _ => triggerUB
        end
      else triggerUB
    else triggerUB
  | _, _ => triggerUB
  end.

  Definition store_bitfield_c (ty: type) 
            (sz: intsize) (sg: signedness) (pos: Z) (width: Z) 
            (addr: val) (v: val) : itree eff val :=
  let chk := (0 <=? pos) && (0 <? width) 
            && (width <=? bitsize_intsize sz) 
            && (pos + width <=? Cop.bitsize_carrier sz) in
  match ty, v, chk with
  | Tint i sg1 attr, Vint n, true =>
    if intsize_eq i sz then
      if signedness_eq sg1
        (if Coqlib.zlt width (bitsize_intsize sz) 
        then Signed else sg) 
      then v <- ccallU "load" (Cop.chunk_for_carrier sz, addr);;
        match v with
        | Vint c => 
          let stored_v := Vint (Int.bitfield_insert (Cop.first_bit sz pos width) width c n) in
          `_ : () <- ccallU "store" (Cop.chunk_for_carrier sz, addr, stored_v);;
          Ret (Vint (Cop.bitfield_normalize sz sg width n))
        | _ => triggerUB
        end
      else triggerUB
    else triggerUB
  | _, _, _ => triggerUB
  end.

  Definition assign_loc_c (ce: composite_env)
           (ty: type) (vp: val)
           (bf: bitfield)
           (v: val): itree eff unit :=
  match access_mode ty, bf with
  | By_value chunk, Full =>
    ccallU "store" (chunk, vp, v)
  | By_copy, Full =>
    match vp, v with
    | Vptr b ofs, Vptr b' ofs' =>
      let chk1 :=
          if (0 <? sizeof ce ty) then
            andb (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs'))
                 (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs))
          else true in
      if negb chk1 then triggerUB else
        let chk2 :=
            (orb (negb (b' =? b))%positive
                 (orb (Ptrofs.unsigned ofs' =? Ptrofs.unsigned ofs)
                      (orb (Ptrofs.unsigned ofs' + sizeof ce ty <=? Ptrofs.unsigned ofs)
                           (Ptrofs.unsigned ofs + sizeof ce ty <=? Ptrofs.unsigned ofs'))))%Z
        in
        if negb chk2 then triggerUB else
          `bytes : list memval <- ccallU "loadbytes" (Vptr b' ofs', sizeof ce ty);;
          ccallU "storebytes" (vp, bytes)
    | _, _ => triggerUB
    end
  | _, Bits sz sg pos width => 
    store_bitfield_c ty sz sg pos width vp v;;; Ret tt
  | _, _ => triggerUB
  end.

  Definition deref_loc_c (ty: type)
             (vp: val) (bf: bitfield): itree eff val :=
    match access_mode ty, bf with
    | By_value chunk, Full => ccallU "load" (chunk, vp)
    | By_reference, Full 
    | By_copy, Full => Ret vp
    | _, Bits sz sg pos width =>
      load_bitfield_c ty sz sg pos width vp
    | _, _ => triggerUB
    end.

  Variable e: Clight.env.
  Variable le: Clight.temp_env.

  Section EVAL_LVALUE.
    Variable _eval_expr_c: expr -> itree eff val.

    Definition _eval_lvalue_c (a: expr)
      : itree eff (val * bitfield) :=
      match a with
      | Evar id ty =>
        match e ! id with
        | Some (l, ty') =>
          if type_eq ty ty' then Ret (Vptr l Ptrofs.zero, Full)
          else triggerUB
        | None =>
          match SkEnv.id2blk skenv (string_of_ident id) with
          | Some i => Ret (Vptr (Pos.of_succ_nat i) Ptrofs.zero, Full)
          | None => triggerUB
          end
        end
      | Ederef a ty =>
        v <- _eval_expr_c a;;
        match v with
        | Vptr l ofs => Ret (Vptr l ofs, Full)
        | _ => triggerUB
        end
      | Efield a i ty =>
        v <- _eval_expr_c a;;
        match v with
        | Vptr l ofs =>
          match Clight.typeof a with
          | Tstruct id att =>
            co <- (ce ! id)?;;
            match field_offset ce i (co_members co) with
            | Errors.OK (delta, bf) =>
              Ret (Vptr l (Ptrofs.add ofs (Ptrofs.repr delta)), bf)
            | _ => triggerUB
            end
          | Tunion id att =>
            co <- (ce ! id)?;;
            match union_field_offset ce i (co_members co) with
            | Errors.OK (delta, bf) =>
                Ret (Vptr l (Ptrofs.add ofs (Ptrofs.repr delta)), bf)
            | _ => triggerUB
            end
          | _ => triggerUB
          end
        | _ => triggerUB
        end
      | _ => triggerUB
      end.

  End EVAL_LVALUE.

  Definition bool_val_c v ty: itree eff bool :=
    match Cop.classify_bool ty with
    | Cop.bool_case_i =>
      match v with
      | Vint n => Ret (negb (Int.eq n Int.zero))
      | Vptr b ofs =>
        if Archi.ptr64
        then triggerUB
        else ccallU "non_null?" v
      | _ => triggerUB
      end
    | Cop.bool_case_l =>
      match v with
      | Vlong n => Ret (negb (Int64.eq n Int64.zero))
      | Vptr b ofs =>
        if negb Archi.ptr64
        then triggerUB
        else ccallU "non_null?" v
      | _ => triggerUB
      end
    | Cop.bool_case_f =>
      match v with
      | Vfloat f => Ret (negb (Floats.Float.cmp Ceq f Floats.Float.zero))
      | _ => triggerUB
      end
    | Cop.bool_case_s =>
      match v with
      | Vsingle f => Ret (negb (Floats.Float32.cmp Ceq f Floats.Float32.zero))
      | _ => triggerUB
      end
    | Cop.bool_default => triggerUB
    end
  .
  
  Definition unary_op_c op v ty: itree eff val :=
    match op with
    | Cop.Onotbool =>
      v <- bool_val_c v ty;; Ret ((Val.of_bool ∘ negb) v)
    | Cop.Onotint => (Cop.sem_notint v ty)?
    | Cop.Oneg => (Cop.sem_neg v ty)?
    | Cop.Oabsfloat => (Cop.sem_absfloat v ty)?
    end
  .

  Definition sem_cast_c v t1 t2: itree eff val :=
    match Cop.classify_cast t1 t2 with
    | Cop.cast_case_pointer =>
      match v with
      | Vint _ => if Archi.ptr64 then triggerUB else Ret v
      | Vlong _ => if Archi.ptr64 then Ret v else triggerUB
      | Vptr _ _ => Ret v
      | _ => triggerUB
      end
    | Cop.cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Ret (Vint (Cop.cast_int_int sz2 si2 i))
      | _ => triggerUB
      end
    | Cop.cast_case_f2f =>
      match v with
      | Vfloat f => Ret (Vfloat f)
      | _ => triggerUB
      end
    | Cop.cast_case_s2s =>
      match v with
      | Vsingle f => Ret (Vsingle f)
      | _ => triggerUB
      end
    | Cop.cast_case_f2s =>
      match v with
      | Vfloat f => Ret (Vsingle (Floats.Float.to_single f))
      | _ => triggerUB
      end
    | Cop.cast_case_s2f =>
      match v with
      | Vsingle f => Ret (Vfloat (Floats.Float.of_single f))
      | _ => triggerUB
      end
    | Cop.cast_case_i2f si1 =>
      match v with
      | Vint i => Ret (Vfloat (Cop.cast_int_float si1 i))
      | _ => triggerUB
      end
    | Cop.cast_case_i2s si1 =>
      match v with
      | Vint i => Ret (Vsingle (Cop.cast_int_single si1 i))
      | _ => triggerUB
      end
    | Cop.cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
        i <- (Cop.cast_float_int si2 f)?;;
        Ret (Vint (Cop.cast_int_int sz2 si2 i))
      | _ => triggerUB
      end
    | Cop.cast_case_s2i sz2 si2 =>
      match v with
      | Vsingle f =>
        i <- (Cop.cast_single_int si2 f)?;; 
        Ret (Vint (Cop.cast_int_int sz2 si2 i))
      | _ => triggerUB
      end
    | Cop.cast_case_l2l =>
      match v with
      | Vlong n => Ret (Vlong n)
      | _ => triggerUB
      end
    | Cop.cast_case_i2l si =>
      match v with
      | Vint n => Ret (Vlong (Cop.cast_int_long si n))
      | _ => triggerUB
      end
    | Cop.cast_case_l2i sz si =>
      match v with
      | Vlong n =>
        Ret (Vint (Cop.cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => triggerUB
      end
    | Cop.cast_case_l2f si1 =>
      match v with
      | Vlong i => Ret (Vfloat (Cop.cast_long_float si1 i))
      | _ => triggerUB
      end
    | Cop.cast_case_l2s si1 =>
      match v with
      | Vlong i => Ret (Vsingle (Cop.cast_long_single si1 i))
      | _ => triggerUB
      end
    | Cop.cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
        i <- (Cop.cast_float_long si2 f)?;;
        Ret (Vlong i)
      | _ => triggerUB
      end
    | Cop.cast_case_s2l si2 =>
      match v with
      | Vsingle f =>
        i <- (Cop.cast_single_long si2 f)?;;
        Ret (Vlong i)
      | _ => triggerUB
      end
    | Cop.cast_case_i2bool =>
      match v with
      | Vint n => Ret (Vint (if Int.eq n Int.zero then Int.zero else Int.one))
      | Vptr b ofs =>
        if Archi.ptr64
        then triggerUB
        else b <- ccallU "non_null?" v;;
             if (b: bool)
             then Ret Vone
             else triggerUB
      | _ => triggerUB
      end
    | Cop.cast_case_l2bool =>
      match v with
      | Vlong n =>
        Ret (Vint (if Int64.eq n Int64.zero then Int.zero else Int.one))
      | Vptr b ofs =>
        if negb Archi.ptr64
        then triggerUB
        else b <- ccallU "non_null?" v;;
             if (b: bool)
             then Ret Vone
             else triggerUB
      | _ => triggerUB
      end
    | Cop.cast_case_f2bool =>
      match v with
      | Vfloat f =>
        Ret (Vint (if Floats.Float.cmp Ceq f Floats.Float.zero
                   then Int.zero
                   else Int.one))
      | _ => triggerUB
      end
    | Cop.cast_case_s2bool =>
      match v with
      | Vsingle f =>
        Ret (Vint (if Floats.Float32.cmp Ceq f Floats.Float32.zero
                   then Int.zero
                   else Int.one))
      | _ => triggerUB
      end
    | Cop.cast_case_struct id1 id2 | Cop.cast_case_union id1 id2 =>
      match v with
      | Vptr _ _ => if ident_eq id1 id2
                    then Ret v else triggerUB
      | _ => triggerUB
      end
    | Cop.cast_case_void => Ret v
    | Cop.cast_case_default => triggerUB
    end.
  
  Definition sem_binarith_c sem_int sem_long sem_float sem_single
             v1 t1 v2 t2: itree eff val :=
    let c := Cop.classify_binarith t1 t2 in
    let t := Cop.binarith_type c in
    v1' <- sem_cast_c v1 t1 t;;
    v2' <- sem_cast_c v2 t2 t;;
    match c with
    | Cop.bin_case_i sg =>
      match v1' with
      | Vint n1 =>
        match v2' with
        | Vint n2 => (sem_int sg n1 n2)?
        | _ => triggerUB
         end
      | _ => triggerUB
      end
    | Cop.bin_case_l sg =>
      match v1' with
      | Vlong n1 =>
        match v2' with
        | Vlong n2 => (sem_long sg n1 n2)?
        | _ => triggerUB
        end
      | _ => triggerUB
      end
    | Cop.bin_case_f =>
      match v1' with
      | Vfloat n1 =>
        match v2' with
        | Vfloat n2 => (sem_float n1 n2)?
        | _ => triggerUB
        end
      | _ => triggerUB
      end
    | Cop.bin_case_s =>
      match v1' with
      | Vsingle n1 =>
        match v2' with
        | Vsingle n2 => (sem_single n1 n2)?
        | _ => triggerUB
        end
      | _ => triggerUB
      end
    | Cop.bin_default => triggerUB
    end.

  Definition sem_add_c cenv v1 t1 v2 t2: itree eff val :=
    match Cop.classify_add t1 t2 with
    | Cop.add_case_pi ty si => (Cop.sem_add_ptr_int cenv ty si v1 v2)?
    | Cop.add_case_pl ty => (Cop.sem_add_ptr_long cenv ty v1 v2)?
    | Cop.add_case_ip si ty => (Cop.sem_add_ptr_int cenv ty si v2 v1)?
    | Cop.add_case_lp ty => (Cop.sem_add_ptr_long cenv ty v2 v1)?
    | Cop.add_default =>
      sem_binarith_c
        (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.add n1 n2)))
        (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.add n1 n2)))
        (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.add n1 n2)))
        (fun n1 n2 : Floats.float32 =>
           Some (Vsingle (Floats.Float32.add n1 n2))) v1 t1 v2 t2
    end.

  Definition sem_sub_c cenv v1 t1 v2 t2: itree eff val :=
    match Cop.classify_sub t1 t2 with
    | Cop.sub_case_pi ty si =>
      match v1 with
      | Vint n1 =>
        match v2 with
        | Vint n2 =>
          if Archi.ptr64 then triggerUB
          else Ret (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
        | _ => triggerUB
        end
      | Vlong n1 =>
        match v2 with
        | Vint n2 =>
          let n3 := Cop.cast_int_long si n2 in
          if negb Archi.ptr64 then triggerUB
          else Ret (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n3)))
        | _ => triggerUB
        end
      | Vptr b1 ofs1 =>
        match v2 with
        | Vint n2 =>
          let n3 := Cop.ptrofs_of_int si n2 in
          Ret (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3)))
        | _ => triggerUB
        end
      | _ => triggerUB
      end
    | Cop.sub_case_pp ty => 
      let sz := sizeof cenv ty in
      ccallU "sub_ptr" (sz, v1, v2)
    | Cop.sub_case_pl ty =>
      match v1 with
      | Vint n1 =>
        match v2 with
        | Vlong n2 =>
          let n3 := Int.repr (Int64.unsigned n2) in
          if Archi.ptr64 then triggerUB
          else Ret (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n3)))
        | _ => triggerUB
        end
      | Vlong n1 =>
        match v2 with
        | Vlong n2 =>
          if negb Archi.ptr64 then triggerUB
          else Ret (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2)))
        | _ => triggerUB
        end
      | Vptr b1 ofs1 =>
        match v2 with
        | Vlong n2 =>
          let n3 := Ptrofs.of_int64 n2 in
          Ret (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n3)))
        | _ => triggerUB
        end
      | _ => triggerUB
      end
    | Cop.sub_default =>
      sem_binarith_c
        (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.sub n1 n2)))
        (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.sub n1 n2)))
        (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.sub n1 n2)))
        (fun n1 n2 : Floats.float32 =>
           Some (Vsingle (Floats.Float32.sub n1 n2))) v1 t1 v2 t2
    end.

  Definition sem_mul_c v1 t1 v2 t2: itree eff val :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.mul n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.mul n1 n2)))
      (fun n1 n2 : Floats.float => Some (Vfloat (Floats.Float.mul n1 n2)))
      (fun n1 n2 : Floats.float32 => Some (Vsingle (Floats.Float32.mul n1 n2)))
      v1 t1 v2 t2.

  Definition sem_div_c v1 t1 v2 t2: itree eff val :=
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

  Definition sem_mod_c v1 t1 v2 t2: itree eff val :=
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
  
  Definition sem_and_c v1 t1 v2 t2: itree eff val :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.and n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.and n1 n2)))
      (fun _ _ : Floats.float => None) (fun _ _ : Floats.float32 => None)
      v1 t1 v2 t2.

  Definition sem_or_c v1 t1 v2 t2: itree eff val :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.or n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.or n1 n2)))
      (fun _ _ : Floats.float => None) (fun _ _ : Floats.float32 => None)
      v1 t1 v2 t2.

  Definition sem_xor_c v1 t1 v2 t2: itree eff val :=
    sem_binarith_c
      (fun (_ : signedness) (n1 n2 : int) => Some (Vint (Int.xor n1 n2)))
      (fun (_ : signedness) (n1 n2 : int64) => Some (Vlong (Int64.xor n1 n2)))
      (fun _ _ : Floats.float => None) (fun _ _ : Floats.float32 => None)
      v1 t1 v2 t2.

  Definition sem_cmp_c c v1 t1 v2 t2: itree eff val :=
    match Cop.classify_cmp t1 t2 with
    | Cop.cmp_case_pp =>
      b <- ccallU "cmp_ptr" (c, v1, v2);; Ret (Val.of_bool b)
    | Cop.cmp_case_pi si =>
      match v2 with
      | Vint n2 =>
        let v2' := Vptrofs (Cop.ptrofs_of_int si n2) in
        b <- ccallU "cmp_ptr" (c, v1, v2');; Ret (Val.of_bool b)
      | Vptr _ _ =>
        if Archi.ptr64 then triggerUB
        else b <- ccallU "cmp_ptr" (c, v1, v2);; Ret (Val.of_bool b)
      | _ => triggerUB
      end
    | Cop.cmp_case_ip si =>
      match v1 with
      | Vint n1 =>
        let v1' := Vptrofs (Cop.ptrofs_of_int si n1) in
        b <- ccallU "cmp_ptr" (c, v1', v2);; Ret (Val.of_bool b)
      | Vptr _ _ =>
        if Archi.ptr64 then triggerUB
        else b <- ccallU "cmp_ptr" (c, v1, v2);; Ret (Val.of_bool b)
      | _ => triggerUB
      end
    | Cop.cmp_case_pl =>
      match v2 with
      | Vlong n2 =>
        let v2' := Vptrofs (Ptrofs.of_int64 n2) in
        b <- ccallU "cmp_ptr" (c, v1, v2');; Ret (Val.of_bool b)
      | Vptr _ _ =>
        if negb Archi.ptr64 then triggerUB
        else b <- ccallU "cmp_ptr" (c, v1, v2);; Ret (Val.of_bool b)
      | _ => triggerUB
      end
    | Cop.cmp_case_lp =>
      match v1 with
      | Vlong n1 =>
        let v1' := Vptrofs (Ptrofs.of_int64 n1) in
        b <- ccallU "cmp_ptr" (c, v1', v2);; Ret (Val.of_bool b)
      | Vptr _ _ =>
        if negb Archi.ptr64 then triggerUB
        else b <- ccallU "cmp_ptr" (c, v1, v2);; Ret (Val.of_bool b)
      | _ => triggerUB
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

  Definition binary_op_c cenv op v1 t1 v2 t2: itree eff val :=
    match op with
    | Cop.Oadd => sem_add_c cenv v1 t1 v2 t2
    | Cop.Osub => sem_sub_c cenv v1 t1 v2 t2
    | Cop.Omul => sem_mul_c v1 t1 v2 t2
    | Cop.Odiv => sem_div_c v1 t1 v2 t2
    | Cop.Omod => sem_mod_c v1 t1 v2 t2
    | Cop.Oand => sem_and_c v1 t1 v2 t2
    | Cop.Oor => sem_or_c v1 t1 v2 t2
    | Cop.Oxor => sem_xor_c v1 t1 v2 t2
    | Cop.Oshl => (Cop.sem_shl v1 t1 v2 t2)?
    | Cop.Oshr => (Cop.sem_shr v1 t1 v2 t2)?
    | Cop.Oeq => sem_cmp_c Ceq v1 t1 v2 t2
    | Cop.One => sem_cmp_c Cne v1 t1 v2 t2
    | Cop.Olt => sem_cmp_c Clt v1 t1 v2 t2
    | Cop.Ogt => sem_cmp_c Cgt v1 t1 v2 t2
    | Cop.Ole => sem_cmp_c Cle v1 t1 v2 t2
    | Cop.Oge => sem_cmp_c Cge v1 t1 v2 t2
    end.
  

  Fixpoint eval_expr_c (expr: Clight.expr): itree eff val :=
    match expr with
    | Econst_int i ty => Ret (Vint i)
    | Econst_float f ty => Ret (Vfloat f)
    | Econst_single f ty => Ret (Vsingle f)
    | Econst_long i ty => Ret (Vlong i)
    | Etempvar id ty => (le ! id)?
    | Eaddrof a ty =>
      '(vp, bf) <- _eval_lvalue_c eval_expr_c a;;
      match bf with
      | Full => Ret vp
      | _ => triggerUB
      end
    | Eunop op a ty =>
      v <- eval_expr_c a;;
      unary_op_c op v (Clight.typeof a)
    | Ebinop op a1 a2 ty =>
      v1 <- eval_expr_c a1;;
      v2 <- eval_expr_c a2;;
      binary_op_c ce op
        v1 (Clight.typeof a1)
        v2 (Clight.typeof a2)
    | Ecast a ty =>
      v <- eval_expr_c a;;
      sem_cast_c v (Clight.typeof a) ty
    | Esizeof ty1 ty =>
      Ret (Vptrofs (Ptrofs.repr (sizeof ce ty1)))
    | Ealignof ty1 ty =>
      Ret (Vptrofs (Ptrofs.repr (alignof ce ty1)))
    | a =>
      '(vp, bf) <- _eval_lvalue_c eval_expr_c a;;
      v <- deref_loc_c (Clight.typeof a) vp bf;; Ret v
    end.

  Definition eval_lvalue_c
    : expr -> itree eff (val * bitfield) :=
    _eval_lvalue_c eval_expr_c.

  Fixpoint eval_exprlist_c
           (es: list expr) (ts: typelist)
    : itree eff (list val) :=
    match es, ts with
    | [], Ctypes.Tnil => Ret []
    | e::es', Ctypes.Tcons ty ts' =>
      v1 <- eval_expr_c e;;
      vs <- eval_exprlist_c es' ts';; 
      v1' <- sem_cast_c v1 (typeof e) ty;;
      Ret (v1':: vs)
    | _, _ => triggerUB
    end.

End EVAL_EXPR_COMP.
End Clight.