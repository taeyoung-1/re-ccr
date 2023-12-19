Require Import CoqlibCCR.
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

Require Import ClightDmExprgen.

Section HIDE.

  Definition hide (p: positive) {A: Type} {a: A} := a.
  Arguments hide _ {A} {a}: simpl never.  

End HIDE.


Section Clight.
Context {eff : Type -> Type}.
Context {HasCall : callE -< eff}.
Context {HasEvent : eventE -< eff}.
Variable ske: Sk.sem.
Let skenv: SkEnv.t := Sk.load_skenv ske.
Variable ce: comp_env.

Definition id_list_norepet_c: list ident -> bool :=
  fun ids => if Coqlib.list_norepet_dec (ident_eq) ids then true else false.

Definition id_list_disjoint_c: list ident -> list ident -> bool :=
  fun ids1 ids2 =>
    if (Coqlib.list_disjoint_dec ident_eq ids1 ids2)
    then true else false.

Fixpoint alloc_variables_c (ce: comp_env) (e: env)
         (vars: list (ident * type))
  : itree eff env := 
  match vars with
  | [] => Ret e
  | (id, ty) :: vars' =>
    v <- ccallU "salloc" (sizeof ce ty);;
    match v with
    | Vptr b ofs => alloc_variables_c ce (alist_add (string_of_ident id) (b, ty) e) vars'
    | _ => triggerUB (* dummy *)
    end
  end.

Definition function_entry_c
           (ce: comp_env) (f: function) (vargs: list val)
  : itree eff (env * temp_env) :=
  if (id_list_norepet_c (var_names (fn_vars f)) &&
      id_list_norepet_c (var_names (fn_params f)) &&
      id_list_disjoint_c (var_names (fn_params f))
                         (var_names (fn_temps f)))%bool
  then
    e <- alloc_variables_c ce [] (fn_vars f);;
    le <- (bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f)))?;;
    Ret (e, le)
  else triggerUB.

Section DECOMP.

  Definition runtime_env : Type := env * temp_env * option bool * option val.

  Notation itr_t := (itree eff runtime_env).

  Definition _sassign_c e le a1 a2 :=
    tau;;
    vp <- eval_lvalue_c ske ce e le a1;;
    v <- eval_expr_c ske ce e le a2;; 
    v' <- sem_cast_c v (typeof a2) (typeof a1);;
    assign_loc_c ce (typeof a1) vp v'.

  Definition _scall_c e le a al
    : itree eff val :=
    match Cop.classify_fun (typeof a) with
    | Cop.fun_case_f tyargs tyres cconv =>
      tau;;
      vf <- eval_expr_c ske ce e le a;;
      vargs <- eval_exprlist_c ske ce e le al tyargs;;
      match vf with
      | Vptr b ofs =>
          if Ptrofs.eq_dec ofs Ptrofs.zero
          then
            '(id, gd) <- (nth_error ske (pred (Pos.to_nat b)))?;;
            fd <- (match gd with inr (Gfun fd) => Some fd | _ => None end)?;;
            if type_eq (type_of_clightdm_fundef fd)
                (Tfunction tyargs tyres cconv)
            then match fd with
                 | CInternal _ => ccallU (string_of_ident id) vargs
                 | CExternal CEF_malloc _ => ccallU "malloc" vargs
                 | CExternal CEF_free _ => ccallU "free" vargs
                 (* this is for builtin memcpy, uncallable in standard C *)
                 (* | External (EF_memcpy al sz) _ _ _ => ccallU "memcpy" (al, sz, vargs) *)
                 | CExternal CEF_capture _ => ccallU "capture" vargs
                 | _ => triggerUB
                 end
            else triggerUB
          else triggerUB
      | _ => triggerUB (* unreachable b*)
      end
    | _ => triggerUB
    end.

  Definition _site_c
             (e: env) (le: temp_env) (a: expr)
    : itree eff bool :=
    tau;;
    v1 <- eval_expr_c ske ce e le a;;
    bool_val_c v1 (typeof a).

  Definition sloop_iter_body_one
             (itr: itr_t)
    : itree eff (env * temp_env * (option (option val))) :=
    '(e', le', obc, v) <- itr;;
    match v with
    | Some retv =>
      (* return *)
      Ret (e', le', Some (Some retv))
    | None =>
        match obc with
        | None => 
        (* skip *)
        tau;;Ret (e', le', None)
        | Some true => 
        (* break, not return *)
        tau;;Ret (e', le', Some None)
        | Some false => 
        (* continue *)
        tau;;Ret (e', le', None)
        end
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
      | Some true => tau;;Ret (e', le', Some None)
      | Some false => triggerUB
      | None => tau;;Ret (e', le', None)
                (* this is for skip *)
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
    '(e1, le1, ov1) <- tau;;sloop_iter_body_one (itr1 e le) ;;
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

  Definition _sloop_itree (p: positive)
             (e: env) (le: temp_env)
             (itr1 itr2: positive -> env -> temp_env -> itr_t)
    : itr_t :=
    '(e', le', v) <-
    ITree.iter (@hide p _ (sloop_iter_body (itr1 (xO p)) (itr2 (xI p)))) (e, le) ;;
    Ret (e', le', None, v).

  Fixpoint free_list_aux (l: list (block * Z)): itree eff unit :=
    match l with
    | nil => Ret tt
    | (b, sz):: l' =>
      `_ : () <- ccallU "sfree" (b, sz);;
      free_list_aux l'
    end.

  Definition block_of_binding (ce: comp_env) (id_b_ty: string * (block * type)) :=
    let (_, p) := id_b_ty in let (b, ty) := p in (b, sizeof ce ty).

  Definition blocks_of_env (ce: comp_env) (le: env) :=
    List.map (block_of_binding ce) le.
  
  Definition _sreturn_c
             (retty: type)
             (e: env) (le: temp_env)
             (oa: option expr)
    : itree eff val :=
    match oa with
    | None => tau;;Ret Vundef
    | Some a =>
      tau;;
      v <- eval_expr_c ske ce e le a;;
      sem_cast_c v (typeof a) retty
    end.

  Fixpoint decomp_stmt (p: positive)
           (retty: type)
           (stmt: statement)
    : env -> temp_env -> itr_t :=
    @hide p _ 
    (fun (e: env) (le: temp_env) =>
    match stmt with
    | Sskip =>
      Ret (e, le, None, None)
    | Sassign a1 a2 =>
      _sassign_c e le a1 a2;;;
      Ret (e, le, None, None)
    | Sset id a =>
      tau;;
      v <- eval_expr_c ske ce e le a ;;
      let le' := alist_add (string_of_ident id) v le in
      Ret (e, le', None, None)
    | Scall optid a al =>
        v <- _scall_c e le a al;;
        Ret (e, (match optid with Some id => alist_add (string_of_ident id) v le | None => le end), None, None)
    | Sbuiltin optid ef tyargs al =>
      tau;;
      vargs <- eval_exprlist_c ske ce e le al tyargs;;
      match ef with
      | EF_malloc => v <- ccallU "malloc" vargs;;
        Ret (e, (match optid with Some id => alist_add (string_of_ident id) v le | None => le end), None, None)
      | EF_free => v <- ccallU "free" vargs;;
        Ret (e, (match optid with Some id => alist_add (string_of_ident id) v le | None => le end), None, None)
      (* this is for builtin memcpy, uncallable in standard C *)
      (* | EF_memcpy al sz => ccallU "memcpy" (al, sz, vargs) *)
      | EF_capture => v <- ccallU "capture" vargs;;
        Ret (e, (match optid with Some id => alist_add (string_of_ident id) v le | None => le end), None, None)
      | _ => triggerUB
      end
    | Ssequence s1 s2 =>
      '(e', le', bc, v) <- tau;;decomp_stmt (xO p) retty s1 e le;;
                        (* this is for steps *)
      match v with
      | Some retval =>
        Ret (e', le', None, v)
      | None =>
        match bc with
        | None =>
          tau;;decomp_stmt (xI p) retty s2 e' le'
        | Some true =>
          tau;;Ret (e', le', bc, None)
        | Some false =>
          tau;;Ret (e', le', bc, None)
        end
      end
    | Sifthenelse a s1 s2 =>
      b <- _site_c e le a;;
      if (b: bool) then (decomp_stmt (xO p) retty s1 e le)
      else (decomp_stmt (xI p) retty s2 e le)
    | Sloop s1 s2 =>
      let itr1 := fun p => decomp_stmt p retty s1 in
      let itr2 := fun p => decomp_stmt p retty s2 in
      _sloop_itree (xO p) e le itr1 itr2
    | Sbreak =>
      Ret (e, le, Some true, None)
    | Scontinue =>
      Ret (e, le, Some false, None)
    | Sreturn oa =>
      v <- _sreturn_c retty e le oa;;
      Ret (e, le, None, Some v)
    | _ =>
      (* not supported *)
      triggerUB
    end).

  Definition decomp_func
           (f: Clight.function)
           (vargs: list val)
    : itree eff val :=
    '(e, le) <- function_entry_c ce (@hide (xO xH) _ f) vargs;;
    '(e', le', c, ov) <- decomp_stmt xH (fn_return f) (fn_body f) e le;; 
    '(_, _, _, v) <- (match ov with
    | Some v => free_list_aux (blocks_of_env ce e');;; Ret (e', le', c, Some v)
    | None => match c : option bool with
              | Some b0 => if b0 then triggerUB else triggerUB
              | None => tau;; free_list_aux (blocks_of_env ce e');;; Ret (e', le', c, Some Vundef)
              end
    end);; v <- v?;;
    Ret v.

  (* Lemma unfold_decomp_stmt :
    decomp_stmt
    = fun retty stmt e le =>
        match stmt with
        | Sskip =>
          Ret (e, le, None, None)
        | Sassign a1 a2 =>
          _sassign_c e le a1 a2;;;
          Ret (e, le, None, None)
        | Sset id a =>
          tau;;
          v <- eval_expr_c sk ce e le a ;;
          let le' := PTree.set id v le in
          Ret (e, le', None, None)
        | Scall optid a al =>
            v <- _scall_c e le a al;;
            Ret (e, (set_opttemp optid v le), None, None)
        | Sbuiltin optid ef tyargs al =>
          tau;;
          vargs <- eval_exprlist_c sk ce e le al tyargs;;
          match ef with
          | EF_malloc => ccallU "malloc" vargs
          | EF_free => ccallU "free" vargs
          (* this is for builtin memcpy, uncallable in standard C *)
          (* | EF_memcpy al sz => ccallU "memcpy" (al, sz, vargs) *)
          | EF_capture => ccallU "capture" vargs
          | _ => triggerUB
          end
        | Ssequence s1 s2 =>
          '(e', le', bc, v) <- tau;;decomp_stmt retty s1 e le;;
                            (* this is for steps *)
          match v with
          | Some retval =>
            Ret (e', le', None, v)
          | None =>
            match bc with
            | None =>
              tau;;decomp_stmt retty s2 e' le'
            | Some true =>
              tau;;Ret (e', le', bc, None)
            | Some false =>
              tau;;Ret (e', le', bc, None)
            end
          end
        | Sifthenelse a s1 s2 =>
          b <- _site_c e le a;;
          if (b: bool) then (decomp_stmt retty s1 e le)
          else (decomp_stmt retty s2 e le)
        | Sloop s1 s2 =>
          let itr1 := decomp_stmt retty s1 in
          let itr2 := decomp_stmt retty s2 in
          _sloop_itree e le itr1 itr2
        | Sbreak =>
          Ret (e, le, Some true, None)
        | Scontinue =>
          Ret (e, le, Some false, None)
        | Sreturn oa =>
          v <- _sreturn_c retty e le oa;;
          Ret (e, le, None, Some v)
        | _ =>
          (* not supported *)
          triggerUB
        end.
    Proof. repeat (apply func_ext; i). destruct x0; et. Qed. *)
  
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

  Definition get_ce (prog: Clight.program) : comp_env :=
    List.map (fun '(id, p) => (string_of_ident id, p)) (PTree.elements prog.(prog_comp_env)).

  (* Context `{SystemEnv}. *)
  Variable prog: Clight.program.
  Let ce: comp_env := get_ce prog.
  Let defs: list (ident * globdef Clight.fundef type) := prog.(prog_defs).
  Let public: list ident := prog.(prog_public).
  Variable mn: string.

  (* Fixpoint get_source_name (filename : string) := *)
  (*   String.substring 0 (String.length filename - 2) filename. *)

  Fixpoint decomp_fundefs (ske: Sk.sem)
           (defs: list (ident * globdef Clight.fundef type))
    : list (ident * (list val -> itree Es val)) :=
    match defs with
    | [] => []
    | (id, gdef) :: defs' =>
      match gdef with
      | Gvar _ => decomp_fundefs ske defs'
      | Gfun fd =>
        match fd with
        | Internal f => 
          (id, fun vl => 
                  v <- decomp_func ske ce f vl;; 
                  (if Pos.eq_dec id (ident_of_string "main")
                   then (match v with Vint _ => Ret v | _ => triggerUB end)
                   else Ret v)) :: decomp_fundefs ske defs'
        | _ => decomp_fundefs ske defs'
        end
      end
    end.
  
  Definition ef2cef (ef: external_function) : extfun :=
    match ef with
    | EF_external _ _ => CEF_external
    | EF_builtin name sg => CEF_builtin name sg 
    | EF_runtime name sg => CEF_runtime name sg
    | EF_vload chunk => CEF_vload chunk
    | EF_vstore chunk => CEF_vstore chunk
    | EF_malloc => CEF_malloc 
    | EF_free => CEF_free 
    | EF_memcpy sz al => CEF_memcpy sz al
    | EF_annot id str typl => CEF_annot id str typl
    | EF_annot_val id str typ => CEF_annot_val id str typ
    | EF_inline_asm str sg strs => CEF_inline_asm str sg strs
    | EF_debug pos id typl => CEF_debug pos id typl
    | EF_capture => CEF_capture
    end.

  Fixpoint get_sk_aux
    (defs: list (ident * globdef Clight.fundef type)) (p: PTree.t clightdm_globaldata) 
      : Sk.t :=
    match defs with
    | [] => p
    | (id, gdef) :: defs' => 
      match gdef with
           | Gvar gv => 
              PTree.set id
                (inr (Gvar (F:=clightdm_fundef) gv))
                (get_sk_aux defs' p)
           | Gfun fd =>
              match fd with
              | Internal f =>
                PTree.set id
                  (inr (Gfun (CInternal (type_of_fundef fd))))
                  (get_sk_aux defs' p)
              | External (EF_external name sg) tyl rty cc =>
                if dec id (ident_of_string name) && signature_eq sg (signature_of_type tyl rty cc)
                then PTree.set id
                      (inr (Gfun (CExternal CEF_external (type_of_fundef fd))))
                      (get_sk_aux defs' p)
                else PTree.set id (inl true) (get_sk_aux defs' p)
              | External ef _ _ _ =>
                PTree.set id
                  (inr (Gfun (CExternal (ef2cef ef) (type_of_fundef fd))))
                  (get_sk_aux defs' p)
              end
            end
    end
  .

  Definition get_sk (defs: list (ident * globdef Clight.fundef type)) : Sk.t :=
    get_sk_aux defs (PTree.empty _).

  Definition modsem (ske: Sk.sem) : ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, f) => (string_of_ident fn, cfunU f)) (decomp_fundefs ske defs);
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
