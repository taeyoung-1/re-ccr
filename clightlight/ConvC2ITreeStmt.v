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

Require Import ConvC2ITree.

Section Clight.
Context {eff : Type -> Type}.
Context {HasCall : callE -< eff}.
Context {HasEvent : eventE -< eff}.
Variable sk: Sk.t.
Let skenv: SkEnv.t := Sk.load_skenv sk.
Variable ce: composite_env.

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
    | _ => triggerUB (* dummy *)
    end
  end.

Definition function_entry_c
           (ce: composite_env) (f: function) (vargs: list val)
  : itree eff (env * temp_env) :=
  if (id_list_norepet_c (var_names (fn_vars f)) &&
      id_list_norepet_c (var_names (fn_params f)) &&
      id_list_disjoint_c (var_names (fn_params f))
                         (var_names (fn_temps f)))%bool
  then
    e <- alloc_variables_c ce empty_env (fn_vars f);;
    le <- (bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f)))?;;
    Ret (e, le)
  else triggerUB.

Section DECOMP.

  Definition runtime_env : Type := env * temp_env * option bool * option val.

  Notation itr_t := (itree eff runtime_env).

  Definition _sassign_c e le a1 a2 :=
    tau;;
    '(loc, (ofs, bf)) <- eval_lvalue_c sk ce e le a1;;
     v <- eval_expr_c sk ce e le a2;; 
     v' <- sem_cast_c v (typeof a2) (typeof a1);;
     v' <- v'?;;
     assign_loc_c ce (typeof a1) loc ofs bf v'.

  Definition _scall_c e le a al
    : itree eff val :=
    match Cop.classify_fun (typeof a) with
    | Cop.fun_case_f tyargs tyres cconv =>
      tau;;
      vf <- eval_expr_c sk ce e le a;;
      vargs <- eval_exprlist_c sk ce e le al tyargs;;
      match vf with
      | Vptr b ofs =>
          '(gsym, skentry) <- (nth_error sk (pred (Pos.to_nat b)))?;;
          `gd : globdef _ type <- (skentry↓)?;;
          fd <- (match gd with Gfun fd => Some fd | _ => None end)?;;
          if type_eq (type_of_fundef fd)
               (Tfunction tyargs tyres cconv)
          then ccallU gsym vargs
          else triggerUB
      | _ => triggerUB (* unreachable b*)
      end
    | _ => triggerUB
    end.

  Definition _site_c
             (e: env) (le: temp_env) (a: expr)
    : itree eff bool :=
    tau;;
    v1 <- eval_expr_c sk ce e le a;;
    b <- bool_val_c v1 (typeof a);;
    b?.

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
      `_ : () <- ccallU "sfree" (b, lo, hi);;
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
    : itree eff val :=
    match oa with
    | None => Ret Vundef
    | Some a =>
      tau;;
      v <- eval_expr_c sk ce e le a;;
      v' <- sem_cast_c v (typeof a) retty;;
      v'?
    end.

  Fixpoint decomp_stmt
           (retty: type)
           (stmt: statement)
           (e: env) (le: temp_env)
    : itr_t :=
    match stmt with
    | Sskip =>
      tau;;Ret (e, le, None, None)
    | Sassign a1 a2 =>
      _sassign_c e le a1 a2;;; tau;;
      Ret (e, le, None, None)
    | Sset id a =>
      tau;;
      v <- eval_expr_c sk ce e le a ;;
      let le' := PTree.set id v le in
      tau;; Ret (e, le', None, None)
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

  Definition decomp_func
           (f: Clight.function)
           (vargs: list val)
    : itree eff val :=
    '(e, le) <- function_entry_c ce f vargs;;
    '(e', _, c, ov) <- decomp_stmt (fn_return f) (fn_body f) e le;; c?;;;
    free_list_aux (blocks_of_env ce e');;;
    match ov with
    | None => Ret Vundef
    | Some v => Ret v
    end.

    Lemma unfold_decomp_stmt :
    decomp_stmt =
  fun retty stmt e le =>
    match stmt with
    | Sskip =>
      tau;;Ret (e, le, None, None)
    | Sassign a1 a2 =>
      _sassign_c e le a1 a2;;; tau;;
      Ret (e, le, None, None)
    | Sset id a =>
      tau;;
      v <- eval_expr_c sk ce e le a ;; 
      let le' := PTree.set id v le in
      tau;; Ret (e, le', None, None)
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
        | Gvar gv => (string_of_ident id, gdef↑) :: get_sk defs'
        | Gfun gf =>
            match gf with
            | Internal f => (string_of_ident id, gdef↑) :: get_sk defs'
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
