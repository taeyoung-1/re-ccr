Require Import Coqlib.
Require Import ITreelib.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight Clightdefs.

Section BODY.
  Context {eff : Type -> Type}.

  Definition cmplu_bool_c m c v1 v2 : itree eff (option bool) :=
    match v1 with
    | Vlong n1 =>
      match v2 with
      | Vlong n2 => Ret (Some (Int64.cmpu c n1 n2))
      | Vptr b2 ofs2 =>
        if negb Archi.ptr64
        then Ret None
        else
          let ret := Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) in
          if Int64.eq n1 Int64.zero && ret
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
          let ret := Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) in
          if Int64.eq n2 Int64.zero && ret
          then Ret (Val.cmp_different_blocks c)
          else Ret None
      | Vptr b2 ofs2 =>
        if negb Archi.ptr64
        then Ret None
        else
          if eq_block b1 b2
          then
            let ret1 := Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) in
            let ret2 := Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) in
            if ret1 && ret2
            then Ret (Some (Ptrofs.cmpu c ofs1 ofs2))
            else Ret None
          else
            let ret1 := Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) in
            let ret2 := Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) in
            if ret1 && ret2
            then Ret (Val.cmp_different_blocks c)
            else Ret None
      | _ => Ret None
      end
    | _ => Ret None
    end.

  Definition cmpu_bool_c m c v1 v2 : itree eff (option bool) :=
    match v1 with
    | Vint n1 =>
      match v2 with
      | Vint n2 => Ret (Some (Int.cmpu c n1 n2))
      | Vptr b2 ofs2 =>
        if negb Archi.ptr64
        then Ret None
        else
          let ret2 := Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) in
          if Int.eq n1 Int.zero && ret2
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
          let ret1 := Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) in
          if Int.eq n2 Int.zero && ret1
          then Ret (Val.cmp_different_blocks c)
          else Ret None
      | Vptr b2 ofs2 =>
        if Archi.ptr64
        then Ret None
        else
          if eq_block b1 b2
          then 
            let ret1 := Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1) in
            let ret2 := Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) in
            if ret1 && ret2
            then Ret (Some (Ptrofs.cmpu c ofs1 ofs2))
            else Ret None
          else
            let ret1 := Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) in
            let ret2 := Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) in
            if ret1 && ret2
            then Ret (Val.cmp_different_blocks c)
            else Ret None
      | _ => Ret None
      end
    | _ => Ret None
    end.
End BODY.