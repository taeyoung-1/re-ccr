Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import ClightDmExprgen ClightDmgen.
From compcertip Require Import Floats Integers Values Ctypes Memory Maps.
From compcertip Require Import Clight Clightdefs.


Section UNFOLD_DECOMP.
  Context `{HasCall : callE -< eff}.
  Context `{HasEvent : eventE -< eff}.

  Lemma decomp_seq (s1 s2 : Clight.statement)
  :
    (fun sk ce retty e le => decomp_stmt sk ce retty (Clight.Ssequence s1 s2) e le)
    = fun sk ce retty e le =>  
      '(e', le', bc, v) <- tau;;decomp_stmt sk ce retty s1 e le;;
      match v with
      | Some retval =>
        Ret (e', le', None, v)
      | None =>
        match bc with
        | None =>
          tau;;decomp_stmt sk ce retty s2 e' le'
        | Some true =>
          tau;;Ret (e', le', bc, None)
        | Some false =>
          tau;;Ret (e', le', bc, None)
        end
      end. 
  Proof. repeat (apply func_ext). refl. Qed.

  Lemma decomp_skip 
  :
    (fun sk ce retty e le => decomp_stmt sk ce retty Clight.Sskip e le)
    = fun sk ce retty e le => Ret (e, le, None, None).
  Proof. repeat (apply func_ext). refl. Qed.

  Lemma decomp_break (retty : type) (e : Clight.env) (le : Clight.temp_env)
    : (fun sk ce retty e le => decomp_stmt sk ce retty Clight.Sbreak e le)
      = fun sk ce retty e le => Ret (e, le, Some true, None).
  Proof. repeat (apply func_ext). refl. Qed.

  Lemma decomp_conti (retty : type) (e : Clight.env) (le : Clight.temp_env) (s1 s2 : Clight.statement)
    : (fun sk ce retty e le => decomp_stmt sk ce retty Clight.Scontinue e le)
      = fun sk ce retty e le => Ret (e, le, Some false, None).
  Proof. repeat (apply func_ext). refl. Qed.
  (* Definition decomp_if (sk : Sk.t) (ce : composite_env) (retty : type)
    (e : Clight.env) (le : Clight.temp_env) (a : Clight.expr) (s1 s2 : Clight.statement)
  :
    decomp_stmt sk ce retty (Clight.Sifthenelse a s1 s2) e le
    = b <- _site_c sk ce e le a;;
      if (b: bool) then (decomp_stmt sk ce retty s1 e le)
      else (decomp_stmt sk ce retty s2 e le) := eq_refl.
  
  Definition decomp_set (sk : Sk.t) (ce : composite_env) (retty : type)
    (e : Clight.env) (le : Clight.temp_env) (id : AST.ident) (a : Clight.expr)
  :
    decomp_stmt sk ce retty (Clight.Sset id a) e le
    = tau;;
      v <- eval_expr_c sk ce e le a ;;
      let le' := PTree.set id v le in
      Ret (e, le', None, None) := eq_refl.

  Definition decomp_asgn (sk : Sk.t) (ce : composite_env) (retty : type)
    (e : Clight.env) (le : Clight.temp_env) (a1 a2 : Clight.expr)
  :
    decomp_stmt sk ce retty (Clight.Sassign a1 a2) e le
    = _sassign_c sk ce e le a1 a2;;; Ret (e, le, None, None) := eq_refl.


  Definition decomp_call (sk : Sk.t) (ce : composite_env) (retty : type)
    (e : Clight.env) (le : Clight.temp_env) (optid : option AST.ident) (a : Clight.expr) (al : list Clight.expr)
  :
    decomp_stmt sk ce retty (Clight.Scall optid a al) e le
    = ` v : val <- _scall_c sk ce e le a al;; Ret (e, Clight.set_opttemp optid v le, None, None) := eq_refl.

  Lemma decomp_loop (retty : type) (e : Clight.env) (le : Clight.temp_env) (s1 s2 : Clight.statement)
    : decomp_stmt ge retty (Clight.Sloop s1 s2) e le
      = let itr1 := decomp_stmt ge retty s1 in
        let itr2 := decomp_stmt ge retty s2 in _sloop_itree e le itr1 itr2.
  Proof. auto. Qed.


  Lemma decomp_ret (retty : type) (e : Clight.env) (le : Clight.temp_env) (oa : option Clight.expr)
    : decomp_stmt ge retty (Clight.Sreturn oa) e le
      = ` v : option val <- _sreturn_c ge retty e le oa;;
        match v with
        | Some v0 => Ret (e, le, None, Some v0)
        | None => triggerUB
    end.
  Proof. auto. Qed. *)

End UNFOLD_DECOMP.