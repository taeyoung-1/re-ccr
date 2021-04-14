(** * The Imp language  *)

(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

Set Implicit Arguments.
(* end hide *)

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : val)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
.

(** function call exists only as a statement *)
Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| Skip                           (* ; *)
| CallFun1 (x : var) (f : gname) (args : list expr) (* x = f(args), call by name *)
| CallFun2 (f : gname) (args : list expr)           (* f(args) *)
| CallPtr1 (x : var) (p : expr) (args : list expr)  (* x = f(args), by pointer*)
| CallPtr2 (p : expr) (args : list expr)            (* f(args) *)
| CallSys1 (x : var) (f : gname) (args : list expr) (* x = f(args), system call *)
| CallSys2 (f : gname) (args : list expr)           (* f(args) *)
| Return1 (e : expr)                                (* return e *)
| Return2                                           (* return *)
| AddrOf (x : var) (X : gname)         (* x = &X *)
| Load (x : var) (p : expr)            (* x = *p *)
| Store (p : expr) (v : expr)          (* *p = v *)
| Cmp (x : var) (a : expr) (b : expr)  (* memory accessing equality comparison *)
.

(** information of a function *)
Record function : Type := mk_function {
  fn_params : list var;
  fn_vars : list var; (* disjoint with fn_params *)
  fn_body : stmt
}.

(* ========================================================================== *)
(** ** Semantics *)

(** Get/Set function local variables *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

(** Get pointer to a global variable/function *)
Variant GlobEnv : Type -> Type :=
| GetPtr (x: gname) : GlobEnv val
| GetName (p: val) : GlobEnv gname.

Section Denote.
 
  Context `{Σ: GRA.t}.
  Context {eff : Type -> Type}.
  Context {HasGlobVar: GlobEnv -< eff}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasCall : callE -< eff}.
  Context {HasEvent : eventE -< eff}.

  (** Denotation of expressions *)
  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => Ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vadd l r)?
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; (vsub l r)?
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vmul l r)?
    end.

  (** Denotation of statements *)
  Definition while (step : itree eff (unit + val)) : itree eff val :=
    ITree.iter (fun _ => step) tt.

  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  Fixpoint denote_exprs (es : list expr) (acc : list val) : itree eff (list val) :=
    match es with
    | [] => Ret acc
    | e :: s =>
      v <- denote_expr e;; denote_exprs s (v::acc)
    end.

  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Assign x e =>
      v <- denote_expr e;; trigger (SetVar x v);; Ret Vundef
    | Seq a b =>
      denote_stmt a;; denote_stmt b
    | If i t e =>
      v <- denote_expr i;; `b: bool <- (is_true v)?;;
      if b then (denote_stmt t) else (denote_stmt e)
    | Skip => Ret Vundef

    | CallFun1 x f args =>
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef
    | CallFun2 f args =>
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        trigger (Call f (eval_args↑));; Ret Vundef

    | CallPtr1 x e args =>
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef
    | CallPtr2 e args =>
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        trigger (Call f (eval_args↑));; Ret Vundef

    | CallSys1 x f args =>
      eval_args <- denote_exprs args [];;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);; Ret Vundef
    | CallSys2 f args =>
      eval_args <- denote_exprs args [];;
      trigger (Syscall f eval_args top1);; Ret Vundef

    | Return1 e => v <- denote_expr e;; Ret v
    | Return2 => Ret Vundef

    | AddrOf x X =>
      v <- trigger (GetPtr X);; trigger (SetVar x v);; Ret Vundef
    | Load x pe =>
      p <- denote_expr pe;;
      v <- trigger (Call "load" (p↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef
    | Store pe ve =>
      p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));; Ret Vundef
    | Cmp x ae be =>
      a <- denote_expr ae;; b <- denote_expr be;;
      v <- trigger (Call "cmp" ([a ; b]↑));; v <- unwrapN (v↓);;
      trigger (SetVar x v);; Ret Vundef

    end.

End Denote.

(* ========================================================================== *)
(** ** Interpretation *)

Section Interp.

  Context `{Σ: GRA.t}.
  Definition effs := GlobEnv +' ImpState +' Es.

  Definition handle_GlobEnv {eff} `{eventE -< eff} (ge: SkEnv.t) : GlobEnv ~> (itree eff) :=
    fun _ e =>
      match e with
      | GetPtr X =>
        r <- (ge.(SkEnv.id2blk) X)?;; Ret (Vptr r 0)
      | GetName p =>
        match p with
        | Vptr n 0 => x <- (ge.(SkEnv.blk2id) n)?;; Ret (x)
        | _ => triggerUB
        end
      end.

  Definition interp_GlobEnv {eff} `{eventE -< eff} (ge: SkEnv.t) : itree (GlobEnv +' eff) ~> (itree eff) :=
    interp (case_ (handle_GlobEnv ge) ((fun T e => trigger e) : eff ~> itree eff)).

  (** function local environment *)
  Definition lenv := alist var val.
  Definition handle_ImpState {eff} `{eventE -< eff} : ImpState ~> stateT lenv (itree eff) :=
    fun _ e le =>
      match e with
      | GetVar x => r <- unwrapU (alist_find _ x le);; Ret (le, r)
      | SetVar x v => Ret (alist_add _ x v le, tt)
      end.

  Definition interp_ImpState {eff} `{eventE -< eff}: itree (ImpState +' eff) ~> stateT lenv (itree eff) :=
    State.interp_state (case_ handle_ImpState ModSem.pure_state).

  Definition interp_imp ge le (itr : itree effs val) :=
    interp_ImpState (interp_GlobEnv ge itr) le.
  
  Fixpoint init_lenv xs : lenv :=
    match xs with
    | [] => []
    | x :: t => (x, Vundef) :: (init_lenv t)
    end
  .

  Fixpoint init_args params args (acc: lenv) : option lenv :=
    match params, args with
    | [], [] => Some acc
    | x :: part, v :: argt =>
      init_args part argt (alist_add _ x v acc)
    | _, _ => None
    end
  .

  Definition eval_imp (ge: SkEnv.t) (f: function) (args: list val) : itree Es val :=
    match (init_args f.(fn_params) args []) with
    | Some iargs =>
      '(_, retv) <- (interp_imp ge (iargs++(init_lenv f.(fn_vars))) (denote_stmt f.(fn_body)));; Ret retv
    | None => triggerUB
    end
  .

End Interp.

(* ========================================================================== *)
(** ** Module *)

(** module components *)
Definition modVars := list (gname * val).
Definition modFuns := list (gname * function).

(** Imp module *)
Record module : Type := mk_module {
  mod_vars : modVars;
  mod_funs : modFuns;
}.

(**** ModSem ****)
Module ImpMod.
Section MODSEML.

  Context `{GRA: GRA.t}.
  Variable mn: mname.
  Variable m: module.

  Set Typeclasses Depth 5.
  (* Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***) *)

  Definition modsem (ge: SkEnv.t) : ModSemL.t := {|
    ModSemL.fnsems :=
      List.map (fun '(fn, f) => (fn, cfun (eval_imp ge f))) m.(mod_funs);
    ModSem.mn := mn;
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}.

  Definition get_mod: Mod.t := {|
    Mod.get_modsem := fun ge => (modsem ge);
    Mod.sk :=
      (List.map (fun '(vn, vv) => (vn, Sk.Gvar vv)) m.(mod_vars)) ++
      (List.map (fun '(fn, _) => (fn, Sk.Gfun)) m.(mod_funs));
  |}.

End MODSEML.
End ImpMod.

(* ========================================================================== *)
(** ** Notations *)

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: val -> expr := Lit.
  Definition Vint_coerce: Z -> val := Vint.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: val >-> expr.
  Coercion Vint_coerce: Z >-> val.

  (* Definition opExpr := option expr. *)
  (* Definition opStr := option string. *)
  (* Definition opStr_coerce: opStr -> opExpr := *)
  (*   (fun os => do s <- os; Some (Var s)). *)
  (* Coercion opStr_coerce: opStr >-> opExpr. *)

  Declare Scope expr_scope.
  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Declare Scope stmt_scope.
  Bind Scope stmt_scope with stmt.

  Notation "x '=#' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a ';#' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  ';#' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'if#' i 'then#' t 'else#' e 'fi#'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'if#'  i '/' '[' 'then#'  t  ']' '/' '[' 'else#'  e ']' '/' 'fi#' ']'").

  Notation "'skip#'" :=
    (Skip) (at level 100): stmt_scope.

  Notation "'ret#'" :=
    (Return2) (at level 60): stmt_scope.

  Notation "'ret#' e" :=
    (Return1 e) (at level 60): stmt_scope.
  
  (* Different methods for function calls *)
  Notation "x '=@' f args" :=
    (CallFun1 x f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "'@' f args" :=
    (CallFun2 f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "x '=@*' fp args" :=
    (CallPtr1 x fp args)
      (at level 60, fp at level 9): stmt_scope.

  Notation "'@*' fp args" :=
    (CallPtr2 fp args)
      (at level 60, fp at level 9): stmt_scope.

  Notation "x '=@!' f args" :=
    (CallSys1 x f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "'@!' f args" :=
    (CallSys2 f args)
      (at level 60, f at level 9): stmt_scope.

  (* interaction with the memory module *)
  Notation "x '=#&' X" :=
    (AddrOf x X) (at level 60): stmt_scope.

  Notation "x '=#' '*' p" :=
    (Load x p) (at level 60): stmt_scope.

  Notation "'*' p '=#' v" :=
    (Store p v) (at level 60): stmt_scope.

  Notation "x '=#' '(' a '==' b ')'" :=
    (Cmp x a b) (at level 60): stmt_scope.

  Notation "x '=#' 'alloc#' s" :=
    (CallFun1 x "alloc" [s])
      (at level 60): stmt_scope.

  Notation "'free#' p" :=
    (CallFun2 "free" [p])
      (at level 60): stmt_scope.

End ImpNotations.

(* ========================================================================== *)
(** ** Example *)
Section Example_Extract.

  Import ImpNotations.
  Let Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition factorial : stmt :=
    if# "input"
    then# "output" =@ "factorial" ["input" - 1%Z] ;#
          "output" =# "input" * "output"
    else# "output" =# 1%Z
    fi#;#
    ret# "output".

  Definition factorial_fundef : function := {|
    fn_params := ["input"];
    fn_vars := ["output"];
    fn_body := factorial
  |}.

  Definition main : stmt :=
    "result" =@ "factorial" [4%Z : expr] ;#
    ret# "result".

  Definition main_fundef : function := {|
    fn_params := [];
    fn_vars := ["result"];
    fn_body := main
  |}.

  Definition ex_extract : module := {|
    mod_vars := [];
    mod_funs := [("factorial", factorial_fundef); ("main", main_fundef)];
  |}.
  
  Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract.

  Definition imp_ex := ModSemL.initial_itr_no_check (ModL.enclose ex_prog).

End Example_Extract.

(* ========================================================================== *)
(** ** Rewriting Leamms *)
Section PROOFS.

  Context `{Σ: GRA.t}.

  (* expr *)
  Lemma denote_expr_Var
        ge le0 v
    :
      interp_imp ge le0 (denote_expr (Var v)) =
      interp_imp ge le0 (trigger (GetVar v)).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Lit
        ge le0 n
    :
      interp_imp ge le0 (denote_expr (Lit n)) =
      interp_imp ge le0 (Ret n).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Plus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Plus a b)) =
      interp_imp ge le0 (l <- denote_expr a ;; r <- denote_expr b ;; (vadd l r)?).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Minus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Minus a b)) =
      interp_imp ge le0 (l <- denote_expr a ;; r <- denote_expr b ;; (vsub l r)?).
  Proof. reflexivity. Qed.

  Lemma denote_expr_Mult
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Mult a b)) =
      interp_imp ge le0 (l <- denote_expr a ;; r <- denote_expr b ;; (vmul l r)?).
  Proof. reflexivity. Qed.

  (* stmt *)
  Lemma denote_stmt_Assign
        ge le0 x e
    :
      interp_imp ge le0 (denote_stmt (Assign x e)) =
      interp_imp ge le0 (v <- denote_expr e ;; trigger (SetVar x v) ;; Ret Vundef).
  Proof. reflexivity. Qed.
  
  Lemma denote_stmt_Seq
        ge le0 a b
    :
      interp_imp ge le0 (denote_stmt (Seq a b)) =
      interp_imp ge le0 (denote_stmt a ;; denote_stmt b).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_If
        ge le0 i t e
    :
      interp_imp ge le0 (denote_stmt (If i t e)) =
      interp_imp ge le0 (v <- denote_expr i ;; `b: bool <- (is_true v)? ;;
      if b then (denote_stmt t) else (denote_stmt e)).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Skip
        ge le0
    :
      interp_imp ge le0 (denote_stmt (Skip)) =
      interp_imp ge le0 (Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Return1
        ge le0 e
    :
      interp_imp ge le0 (denote_stmt (Return1 e)) =
      interp_imp ge le0 (v <- denote_expr e;; Ret v).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Return2
        ge le0
    :
      interp_imp ge le0 (denote_stmt (Return2)) =
      interp_imp ge le0 (Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_AddrOf
        ge le0 x X
    :
      interp_imp ge le0 (denote_stmt (AddrOf x X)) =
      interp_imp ge le0 (v <- trigger (GetPtr X);; trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Load
        ge le0 x pe
    :
      interp_imp ge le0 (denote_stmt (Load x pe)) =
      interp_imp ge le0 (p <- denote_expr pe;;
      v <- trigger (Call "load" (p↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Store
        ge le0 pe ve
    :
      interp_imp ge le0 (denote_stmt (Store pe ve)) =
      interp_imp ge le0 (p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Cmp
        ge le0 x ae be
    :
      interp_imp ge le0 (denote_stmt (Cmp x ae be)) =
      interp_imp ge le0 ( a <- denote_expr ae;; b <- denote_expr be;;
      v <- trigger (Call "cmp" ([a ; b]↑));; v <- unwrapN (v↓);;
      trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallFun1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallFun1 x f args)) =
      interp_imp ge le0 (
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallFun2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallFun2 f args)) =
      interp_imp ge le0 (
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        trigger (Call f (eval_args↑));; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallPtr1
        ge le0 x e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr1 x e args)) =
      interp_imp ge le0 (
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.
  
  Lemma denote_stmt_CallPtr2
        ge le0 e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr2 e args)) =
      interp_imp ge le0 (
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store") || String.string_dec f "cmp"
      then triggerUB
      else
        eval_args <- (denote_exprs args []);;
        trigger (Call f (eval_args↑));; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallSys1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallSys1 x f args)) =
      interp_imp ge le0 (
      eval_args <- (denote_exprs args []);;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);; Ret Vundef).
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallSys2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallSys2 f args)) =
      interp_imp ge le0 (
      eval_args <- (denote_exprs args []);;
      trigger (Syscall f eval_args top1);; Ret Vundef).
  Proof. reflexivity. Qed.

  (* interp_imp *)

  Lemma interp_imp_bind
        itr ktr ge le0
    :
      interp_imp ge le0 (v <- itr ;; ktr v) =
      '(le1, v) <- interp_imp ge le0 itr ;;
      interp_imp ge le1 (ktr v).
  Proof.
    unfold interp_imp. unfold interp_GlobEnv.
    unfold interp_ImpState. grind. des_ifs.
  Qed.

  Lemma interp_imp_tau
        itr ge le0
    :
      interp_imp ge le0 (tau;; itr) =
      tau;; interp_imp ge le0 itr.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_Ret
        ge le0 v
    :
      interp_imp ge le0 (Ret v) = Ret (le0, v).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_triggerUB
        ge le0
    :
      (interp_imp ge le0 (triggerUB) : itree Es _) = triggerUB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerUB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerNB
        ge le0
    :
      (interp_imp ge le0 (triggerNB) : itree Es _) = triggerNB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerNB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_unwrapU
        x ge le0
    :
      interp_imp ge le0 (unwrapU x) =
      x <- unwrapU x;; Ret (le0, x).
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerUB.
      unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_unwrapN
        x ge le0
    :
      interp_imp ge le0 (unwrapN x) =
      x <- unwrapN x;; Ret (le0, x).
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerNB.
      unfold triggerNB. grind.
  Qed.

  Lemma interp_imp_GetPtr
        ge le0 X
    :
      interp_imp ge le0 (trigger (GetPtr X)) =
      r <- (ge.(SkEnv.id2blk) X)? ;; tau;; Ret (le0, Vptr r 0).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, unwrapU.
    des_ifs; grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. unfold triggerUB, pure_state. grind.
  Qed.

  Lemma interp_imp_GetVar
        ge le0 x
    :
      (interp_imp ge le0 (trigger (GetVar x)) : itree Es _) =
      r <- unwrapU (alist_find _ x le0);; tau;; tau;; Ret (le0, r).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_SetVar_Vundef
        ge le0 x v
    :
      interp_imp ge le0 (trigger (SetVar x v) ;; Ret Vundef) =
      tau;; tau;; Ret (alist_add _ x v le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Call_only
        ge le0 f args
    :
      interp_imp ge le0 (trigger (Call f args);; Ret Vundef) =
      trigger (Call f args);; tau;; tau;; Ret (le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Call_ret
        ge le0 f args x
    :
      interp_imp ge le0
                 (v <- trigger (Call f args);; v <- unwrapN (v↓);;
                  trigger (SetVar x v);; Ret Vundef) =
      v <- trigger (Call f args);;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add _ x v le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
    unfold unwrapN. des_ifs; grind.
    - rewrite interp_trigger. grind.
    - unfold triggerNB. grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Syscall_only
        ge le0 f args
    :
      interp_imp ge le0 (trigger (Syscall f args top1);; Ret Vundef) =
      trigger (Syscall f args top1);; tau;; tau;; Ret (le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Syscall_ret
        ge le0 f args x
    :
      interp_imp ge le0
                 (v <- trigger (Syscall f args top1);;
                  trigger (SetVar x v);; Ret Vundef) =
      v <- trigger (Syscall f args top1);;
      tau;; tau;; tau;; tau;;
      Ret (alist_add _ x v le0, Vundef).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    unfold pure_state. rewrite interp_trigger. grind.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_expr_Var
        ge le0 v
    :
      interp_imp ge le0 (denote_expr (Var v)) =
      r <- unwrapU (alist_find _ v le0);; tau;; tau;; Ret (le0, r).
  Proof.
    apply interp_imp_GetVar.
  Qed.

  Lemma interp_imp_expr_Lit
        ge le0 n
    :
      interp_imp ge le0 (denote_expr (Lit n)) =
      Ret (le0, n).
  Proof.
    rewrite denote_expr_Lit. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Plus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Plus a b)) =
      '(le1, l) <- interp_imp ge le0 (denote_expr a) ;;
      '(le2, r) <- interp_imp ge le1 (denote_expr b) ;;
      v <- (vadd l r)? ;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Plus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    apply interp_imp_unwrapU.
  Qed.

  Lemma interp_imp_expr_Minus
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Minus a b)) =
      '(le1, l) <- interp_imp ge le0 (denote_expr a) ;;
      '(le2, r) <- interp_imp ge le1 (denote_expr b) ;;
      v <- (vsub l r)? ;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Minus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    apply interp_imp_unwrapU.
  Qed.

  Lemma interp_imp_expr_Mult
        ge le0 a b
    :
      interp_imp ge le0 (denote_expr (Mult a b)) =
      '(le1, l) <- interp_imp ge le0 (denote_expr a) ;;
      '(le2, r) <- interp_imp ge le1 (denote_expr b) ;;
      v <- (vmul l r)? ;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Mult. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    apply interp_imp_unwrapU.
  Qed.

  Lemma interp_imp_Assign
        ge le0 x e
    :
      interp_imp ge le0 (denote_stmt (Assign x e)) =
      '(le1, v) <- interp_imp ge le0 (denote_expr e) ;;
      tau;; tau;; Ret (alist_add _ x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Assign.
    rewrite interp_imp_bind. grind.
    apply interp_imp_SetVar_Vundef.
  Qed.

  Lemma interp_imp_Seq
        ge le0 a b
    :
      interp_imp ge le0 (denote_stmt (Seq a b)) =
      '(le1, _) <- interp_imp ge le0 (denote_stmt a) ;;
      interp_imp ge le1 (denote_stmt b).
  Proof.
    rewrite denote_stmt_Seq.
    apply interp_imp_bind.
  Qed.

  Lemma interp_imp_If
        ge le0 i t e
    :
      interp_imp ge le0 (denote_stmt (If i t e)) =
      '(le1, v) <- interp_imp ge le0 (denote_expr i) ;;
      `b: bool <- (is_true v)? ;;
       if b
       then interp_imp ge le1 (denote_stmt t)
       else interp_imp ge le1 (denote_stmt e).
  Proof.
    rewrite denote_stmt_If. rewrite interp_imp_bind.
    grind. destruct (is_true v); grind; des_ifs.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    unfold triggerUB, pure_state. grind.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Skip
        ge le0
    :
      interp_imp ge le0 (denote_stmt (Skip)) =
      Ret (le0, Vundef).
  Proof.
    rewrite denote_stmt_Skip. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Return1
        ge le0 e
    :
      interp_imp ge le0 (denote_stmt (Return1 e)) =
      '(le1, v) <- interp_imp ge le0 (denote_expr e) ;;
      Ret (le1, v).
  Proof.
    rewrite denote_stmt_Return1. rewrite interp_imp_bind.
    grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Return2
        ge le0
    :
      interp_imp ge le0 (denote_stmt (Return2)) =
      Ret (le0, Vundef).
  Proof.
    rewrite denote_stmt_Return2. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_AddrOf
        ge le0 x X
    :
      interp_imp ge le0 (denote_stmt (AddrOf x X)) =
      r <- (ge.(SkEnv.id2blk) X)? ;; tau;;
      tau;; tau;; Ret (alist_add _ x (Vptr r 0) le0, Vundef).
  Proof.
    rewrite denote_stmt_AddrOf. rewrite interp_imp_bind.
    rewrite interp_imp_GetPtr. grind.
    apply interp_imp_SetVar_Vundef.
  Qed.

  Lemma interp_imp_Load
        ge le0 x pe
    :
      interp_imp ge le0 (denote_stmt (Load x pe)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr pe);;
      v <- trigger (Call "load" (p↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add _ x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Load. rewrite interp_imp_bind.
    grind. apply interp_imp_Call_ret.
  Qed.

  Lemma interp_imp_Store
        ge le0 pe ve
    :
      interp_imp ge le0 (denote_stmt (Store pe ve)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr pe);;
      '(le2, v) <- interp_imp ge le1 (denote_expr ve);;
      trigger (Call "store" ([p ; v]↑));; tau;; tau;; Ret (le2, Vundef).
  Proof.
    rewrite denote_stmt_Store. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    apply interp_imp_Call_only.
  Qed.

  Lemma interp_imp_Cmp
        ge le0 x ae be
    :
      interp_imp ge le0 (denote_stmt (Cmp x ae be)) =
      '(le1, a) <- interp_imp ge le0 (denote_expr ae);;
      '(le2, b) <- interp_imp ge le1 (denote_expr be);;
      v <- trigger (Call "cmp" ([a ; b]↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add _ x v le2, Vundef).
  Proof.
    rewrite denote_stmt_Cmp. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    apply interp_imp_Call_ret.
  Qed.

  Fixpoint interp_imp_denote_exprs ge le h es acc :=
    match es with
    | [] =>
      '(le1, v) <- interp_imp ge le (denote_expr h);;
      Ret (le1, v::acc)
    | e :: s =>
      '(le1, v) <- interp_imp ge le (denote_expr h);;
      interp_imp_denote_exprs ge le1 e s (v::acc)
    end.

  Lemma interp_imp_exprs
        ge le0 x f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
                   trigger (SetVar x v);; Ret Vundef)
      =
      match args with
      | [] =>
        v <- trigger (Call f ((acc : list val)↑));;
        tau;; tau;; v <- unwrapN (v↓);;
        tau;; tau;; Ret (alist_add _ x v le0, Vundef)
      | h::t =>
        '(le1, vs) <- interp_imp_denote_exprs ge le0 h t acc;;
        v <- trigger (Call f (vs↑));;
        tau;; tau;; v <- unwrapN (v↓);;
        tau;; tau;; Ret (alist_add _ x v le1, Vundef)
      end.
  Proof.
    destruct args.
    - ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      rewrite <- (interp_imp_Call_ret ge).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    - move args before Σ. revert_until args. induction args; i.
      + ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
        rewrite <- (interp_imp_Call_ret ge).
        unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      + ss. grind. rewrite interp_imp_bind. grind.
        destruct x0. ss.
  Qed.

  Lemma interp_imp_exprs_only
        ge le0 f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   trigger (Call f (eval_args↑));; Ret Vundef)
      =
      match args with
      | [] =>
        trigger (Call f ((acc : list val)↑));;
        tau;; tau;; Ret (le0, Vundef)
      | h::t =>
        '(le1, vs) <- interp_imp_denote_exprs ge le0 h t acc;;
        trigger (Call f (vs↑));;
        tau;; tau;; Ret (le1, Vundef)
      end.
  Proof.
    destruct args.
    - ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      rewrite <- (interp_imp_Call_only ge).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    - move args before Σ. revert_until args. induction args; i.
      + ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
        rewrite <- (interp_imp_Call_only ge).
        unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      + ss. grind. rewrite interp_imp_bind. grind.
        destruct x. ss.
  Qed.

  Lemma interp_imp_CallFun1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallFun1 x f args)) =
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        match args with
        | [] =>
          v <- trigger (Call f ([]: list val)↑);;
          tau;; tau;; v <- unwrapN (v↓);;
          tau;; tau;; Ret (alist_add _ x v le0, Vundef)
        | h::t =>
          '(le1, vs) <- interp_imp_denote_exprs ge le0 h t [];;
          v <- trigger (Call f (vs↑));;
          tau;; tau;; v <- unwrapN (v↓);;
          tau;; tau;; Ret (alist_add _ x v le1, Vundef)
        end.
  Proof.
    rewrite denote_stmt_CallFun1. des_ifs; try (apply interp_imp_exprs).
    apply interp_imp_triggerUB.
  Qed.

  Lemma interp_imp_CallFun2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallFun2 f args)) =
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        match args with
        | [] =>
          trigger (Call f ([]: list val)↑);;
          tau;; tau;; Ret (le0, Vundef)
        | h::t =>
          '(le1, vs) <- interp_imp_denote_exprs ge le0 h t [];;
          trigger (Call f (vs↑));;
          tau;; tau;; Ret (le1, Vundef)
        end.
  Proof.
    rewrite denote_stmt_CallFun2. des_ifs; try (apply interp_imp_exprs_only).
    apply interp_imp_triggerUB.
  Qed.

  Lemma interp_imp_CallPtr1
        ge le0 x e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr1 x e args)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr e);;
      match p with
      | Vptr n 0 =>
        match (SkEnv.blk2id ge n) with
        | Some f =>
          if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
          then tau;; triggerUB
          else
            match args with
            | [] =>
              tau;;
              v <- trigger (Call f ([]: list val)↑);;
              tau;; tau;; v <- unwrapN (v↓);;
              tau;; tau;; Ret (alist_add _ x v le1, Vundef)
            | h::t =>
              tau;;
              '(le2, vs) <- interp_imp_denote_exprs ge le1 h t [];;
              v <- trigger (Call f (vs↑));;
              tau;; tau;; v <- unwrapN (v↓);;
              tau;; tau;; Ret (alist_add _ x v le2, Vundef)
            end
        | None => triggerUB
        end
      | _ => triggerUB
      end.
  Proof.
    rewrite denote_stmt_CallPtr1. rewrite interp_imp_bind.
    grind. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    des_ifs; grind; rewrite interp_trigger.
    1, 2, 5, 6, 7, 8:( unfold triggerUB, pure_state; grind; unfold triggerUB; grind ).
    1, 2:( unfold unwrapU, triggerUB; des_ifs; grind; rewrite interp_trigger; grind ).
    - rewrite <- (interp_imp_exprs ge) with (args := []).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      unfold pure_state. rewrite interp_trigger. grind.
      unfold unwrapU, triggerUB; grind.
      rewrite interp_trigger; grind.
    - rewrite <- (interp_imp_exprs ge) with (args := (e0::l0)).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      unfold pure_state, unwrapU, triggerUB; grind.
  Qed.

  Lemma interp_imp_CallPtr2
        ge le0 e args
    :
      interp_imp ge le0 (denote_stmt (CallPtr2 e args)) =
      '(le1, p) <- interp_imp ge le0 (denote_expr e);;
      match p with
      | Vptr n 0 =>
        match (SkEnv.blk2id ge n) with
        | Some f =>
          if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
          then tau;; triggerUB
          else
            match args with
            | [] =>
              tau;;
              trigger (Call f ([]: list val)↑);;
              tau;; tau;; Ret (le1, Vundef)
            | h::t =>
              tau;;
              '(le2, vs) <- interp_imp_denote_exprs ge le1 h t [];;
              trigger (Call f (vs↑));;
              tau;; tau;; Ret (le2, Vundef)
            end
        | None => triggerUB
        end
      | _ => triggerUB
      end.
  Proof.
    rewrite denote_stmt_CallPtr2. rewrite interp_imp_bind.
    grind. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    des_ifs; grind; rewrite interp_trigger.
    1, 2, 5, 6, 7, 8:( unfold triggerUB, pure_state; grind; unfold triggerUB; grind ).
    1, 2:( unfold unwrapU, triggerUB; des_ifs; grind; rewrite interp_trigger; grind ).
    - rewrite <- (interp_imp_exprs_only ge) with (args := []).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      unfold pure_state. rewrite interp_trigger. grind.
      unfold unwrapU, triggerUB; grind.
      rewrite interp_trigger; grind.
    - rewrite <- (interp_imp_exprs_only ge) with (args := (e0::l0)).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      unfold pure_state, unwrapU, triggerUB; grind.
  Qed.

  Lemma interp_imp_exprs_sys
        ge le0 x f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   v <- trigger (Syscall f eval_args top1);;
                   trigger (SetVar x v);; Ret Vundef)
      =
      match args with
      | [] =>
        v <- trigger (Syscall f ((acc : list val)) top1);;
        tau;; tau;; tau;; tau;;
        Ret (alist_add _ x v le0, Vundef)
      | h::t =>
        '(le1, vs) <- interp_imp_denote_exprs ge le0 h t acc;;
        v <- trigger (Syscall f vs top1);;
        tau;; tau;; tau;; tau;;
        Ret (alist_add _ x v le1, Vundef)
      end.
  Proof.
    destruct args.
    - ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      rewrite <- (interp_imp_Syscall_ret ge).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    - move args before Σ. revert_until args. induction args; i.
      + ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
        rewrite <- (interp_imp_Syscall_ret ge).
        unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      + ss. grind. rewrite interp_imp_bind. grind.
        destruct x0. ss.
  Qed.

  Lemma interp_imp_exprs_sys_only
        ge le0 f args acc
    :
      interp_imp ge le0 (
                   eval_args <- (denote_exprs args acc);;
                   trigger (Syscall f eval_args top1);; Ret Vundef)
      =
      match args with
      | [] =>
        trigger (Syscall f (acc : list val) top1);;
        tau;; tau;; Ret (le0, Vundef)
      | h::t =>
        '(le1, vs) <- interp_imp_denote_exprs ge le0 h t acc;;
        trigger (Syscall f vs top1);;
        tau;; tau;; Ret (le1, Vundef)
      end.
  Proof.
    destruct args.
    - ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      rewrite <- (interp_imp_Syscall_only ge).
      unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
    - move args before Σ. revert_until args. induction args; i.
      + ss. unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
        rewrite <- (interp_imp_Syscall_only ge).
        unfold interp_imp, interp_GlobEnv, interp_ImpState. grind.
      + ss. grind. rewrite interp_imp_bind. grind.
        destruct x. ss.
  Qed.

  Lemma interp_imp_CallSys1
        ge le0 x f args
    :
      interp_imp ge le0 (denote_stmt (CallSys1 x f args)) =
      match args with
      | [] =>
        v <- trigger (Syscall f ([]: list val) top1);;
        tau;; tau;; tau;; tau;;
        Ret (alist_add _ x v le0, Vundef)
      | h::t =>
        '(le1, vs) <- interp_imp_denote_exprs ge le0 h t [];;
        v <- trigger (Syscall f vs top1);;
        tau;; tau;; tau;; tau;;
        Ret (alist_add _ x v le1, Vundef)
      end.
  Proof.
    rewrite denote_stmt_CallSys1. apply interp_imp_exprs_sys.
  Qed.

  Lemma interp_imp_CallSys2
        ge le0 f args
    :
      interp_imp ge le0 (denote_stmt (CallSys2 f args)) =
      match args with
      | [] =>
        trigger (Syscall f ([]: list val) top1);;
        tau;; tau;;
        Ret (le0, Vundef)
      | h::t =>
        '(le1, vs) <- interp_imp_denote_exprs ge le0 h t [];;
        trigger (Syscall f vs top1);;
        tau;; tau;;
        Ret (le1, Vundef)
      end.
  Proof.
    rewrite denote_stmt_CallSys2. apply interp_imp_exprs_sys_only.
  Qed.

  (* eval_imp  *)
  Lemma unfold_eval_imp
        ge fparams fvars fbody args
    :
      ` vret : val <- eval_imp ge (mk_function fparams fvars fbody) args ;; Ret (vret↑)
               =
               ` vret : val <-
                        (match init_args fparams args [] with
                         | Some iargs =>
                           ITree.bind (interp_imp ge (iargs++(init_lenv (fvars))) (denote_stmt fbody))
                                      (fun x_ : lenv * val => let '(_, retv) := x_ in Ret retv)
                         | None => triggerUB
                         end) ;; Ret (vret↑).
  Proof. reflexivity. Qed.

End PROOFS.

(** tactics **)
Global Opaque denote_expr.
Global Opaque denote_stmt.
Global Opaque interp_imp.
Global Opaque eval_imp.

Require Import SimModSem.
Require Import HTactics.

Import ImpNotations.
(** tactic for imp-program reduction *)
Ltac imp_red :=
  cbn;
  match goal with
  (** denote_stmt *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp _ _ (denote_stmt (?stmt))))) ] =>
    match stmt with
    | Assign _ _ => rewrite interp_imp_Assign
    | Seq _ _ => rewrite interp_imp_Seq; imp_red
    | If _ _ _ => rewrite interp_imp_If
    | Skip => rewrite interp_imp_Skip
    | CallFun1 _ _ _ => rewrite interp_imp_CallFun1
    | CallFun2 _ _ => rewrite interp_imp_CallFun2
    | CallPtr1 _ _ _ => rewrite interp_imp_CallPtr1
    | CallPtr2 _ _ => rewrite interp_imp_CallPtr2
    | CallSys1 _ _ _ => rewrite interp_imp_CallSys1
    | CallSys2 _ _ => rewrite interp_imp_CallSys2
    | Return1 _ => rewrite interp_imp_Return1
    | Return2 => rewrite interp_imp_Return2
    | AddrOf _ _ => rewrite interp_imp_AddrOf
    | Load _ _ => rewrite interp_imp_Load
    | Store _ _ => rewrite interp_imp_Store
    | Cmp _ _ _ => rewrite interp_imp_Cmp
    | _ => fail
    end

      (** denote_expr *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp _ _ (denote_expr (?expr))))) ] =>
    match expr with
    | Var _ => rewrite interp_imp_expr_Var
    | Lit _ => rewrite interp_imp_expr_Lit
    | Plus _ _ => rewrite interp_imp_expr_Plus
    | Minus _ _ => rewrite interp_imp_expr_Minus
    | Mult _ _ => rewrite interp_imp_expr_Mult
    | Var_coerce _ => rewrite interp_imp_expr_Var
    | Lit_coerce _ => rewrite interp_imp_expr_Lit
    | _ => fail
    end

  | _ => idtac
  end.

Ltac imp_steps := repeat (repeat imp_red; steps).
