 Require Import Coqlib AList.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.
Require Import Any.
Require Import IRed.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.



(*** TODO: move to ITreelib, and replace raw definitions with this ***)
Definition trivial_Handler `{E -< F}: Handler E F := fun T X => trigger X.

Inductive ord: Type :=
| ord_pure (n: Ord.t)
| ord_top
.

Definition is_pure (o: ord): bool := match o with | ord_pure _ => true | _ => false end.

Definition ord_lt (next cur: ord): Prop :=
  match next, cur with
  | ord_pure next, ord_pure cur => (next < cur)%ord
  | _, ord_top => True
  | _, _ => False
  end
.

(**
(defface hi-light-green-b
  '((((min-colors 88)) (:weight bold :foreground "dark magenta"))
    (t (:weight bold :foreground "dark magenta")))
  "Face for hi-lock mode."
  :group 'hi-lock-faces)

 **)


Section PSEUDOTYPING.

(*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)

Require Import IPM.

Section FSPEC.
  Context `{Σ: GRA.t}.

  (*** spec table ***)
  Record fspec: Type := mk_fspec {
    meta: Type;
    measure: meta -> ord;
    precond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
    postcond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
  }
  .

  Definition mk (X AA AR: Type) (measure: X -> ord) (precond: X -> AA -> Any_tgt -> iProp) (postcond: X -> AR -> Any_tgt -> iProp) :=
    @mk_fspec
      X
      measure
      (fun x arg_src arg_tgt => (∃ (aa: AA), ⌜arg_src = aa↑⌝ ∧ precond x aa arg_tgt)%I)
      (fun x ret_src ret_tgt => (∃ (ar: AR), ⌜ret_src = ar↑⌝ ∧ postcond x ar ret_tgt)%I)
  .

  Definition fspec_trivial: fspec :=
    mk_fspec (meta:=unit) (fun _ => ord_top) (fun _ argh argl => (⌜argh = argl⌝: iProp)%I)
             (fun _ reth retl => (⌜reth = retl⌝: iProp)%I)
  .
End FSPEC.


Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.


  Definition mput E `{sE -< E} `{eventE -< E} (mr: Σ): itree E unit :=
    st <- trigger sGet;; '(mp, _) <- ((Any.split st)?);;
    trigger (sPut (Any.pair mp mr↑))
  .

  Definition mget E `{sE -< E} `{eventE -< E}: itree E Σ :=
    st <- trigger sGet;; '(_, mr) <- ((Any.split st)?);;
    mr↓?
  .

  Definition pupdate E `{sE -< E} `{eventE -< E} {X} (run: Any.t -> Any.t * X) : itree E X :=
    trigger (SUpdate (fun st => 
      match (Any.split st) with
      | Some (x, mr) => ((Any.pair (fst (run x)) mr), snd (run x))
      | None => run tt↑
      end
    ))
  .


  Definition ASSUME (Cond: Any.t -> Any.t -> iProp) (valp: Any.t): stateT Σ (itree Es) Any.t :=
    fun fr =>
      '(cres, ctx) <- trigger (Take (Σ * Σ));;
      mr <- mget;;
      assume(URA.wf (cres ⋅ fr ⋅ ctx ⋅ mr));;;
      valv <- trigger (Take Any.t);;
      assume(Cond valv valp cres);;;
      Ret (ctx, valv)
  .

  Definition ASSERT (Cond: Any.t -> Any.t -> iProp) (valv: Any.t): stateT Σ (itree Es) Any.t :=
    fun ctx =>
      '(cres, fr, mr) <- trigger (Choose (Σ * Σ * Σ));;
      mput mr;;;
      guarantee(URA.wf (cres ⋅ fr ⋅ ctx ⋅ mr));;;
      valp <- trigger (Choose Any.t);;
      guarantee(Cond valv valp cres);;;
      Ret (fr, valp)
  .


  Definition HoareCall
             (tbr: bool)
             (ord_cur: ord)
             (fsp: fspec):
    gname -> Any.t -> stateT (Σ) (itree Es) Any.t :=
    fun fn varg_src ctx =>

      x <- trigger (Choose fsp.(meta));;
      '(fr, varg_tgt) <- (ASSERT (fsp.(precond) x) varg_src ctx);;

      let ord_next := fsp.(measure) x in
      guarantee(ord_lt ord_next ord_cur /\ (tbr = true -> is_pure ord_next) /\ (tbr = false -> ord_next = ord_top));;;

      vret_tgt <- trigger (Call fn varg_tgt);;

      ASSUME (fsp.(postcond) x) vret_tgt fr
  .

End PROOF.















(*** TODO: Move to Coqlib. TODO: Somehow use case_ ??? ***)
(* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b). *)
(* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b). *)

Variant hCallE: Type -> Type :=
| hCall (tbr: bool) (fn: gname) (varg_src: Any_src): hCallE Any_src
(*** tbr == to be removed ***)
.

Variant hAPCE: Type -> Type :=
| hAPC: hAPCE unit
.

Notation Es' := (hCallE +' sE +' eventE).

Definition hEs := (hAPCE +' Es).

Definition hcall {X Y} (fn: gname) (varg: X): itree (hCallE +' sE +' eventE) Y :=
  vret <- trigger (hCall false fn varg↑);; vret <- vret↓ǃ;; Ret vret.

Program Fixpoint _APC (at_most: Ord.t) {wf Ord.lt at_most}: itree Es' unit :=
  break <- trigger (Choose _);;
  if break: bool
  then Ret tt
  else
    n <- trigger (Choose Ord.t);;
    trigger (Choose (n < at_most)%ord);;;
    '(fn, varg) <- trigger (Choose _);;
    trigger (hCall true fn varg);;;
    _APC n.
Next Obligation.
  i. auto.
Qed.
Next Obligation.
  eapply Ord.lt_well_founded.
Qed.

Definition APC: itree Es' unit :=
  at_most <- trigger (Choose _);;
  _APC at_most
.

Lemma unfold_APC:
  forall at_most, _APC at_most =
                  break <- trigger (Choose _);;
                  if break: bool
                  then Ret tt
                  else
                    n <- trigger (Choose Ord.t);;
                    guarantee (n < at_most)%ord;;;
                    '(fn, varg) <- trigger (Choose _);;
                    trigger (hCall true fn varg);;;
                    _APC n.
Proof.
  i. unfold _APC. rewrite Fix_eq; eauto.
  { repeat f_equal. extensionality break. destruct break; ss.
    repeat f_equal. extensionality n.
    unfold guarantee. rewrite bind_bind.
    repeat f_equal. extensionality p.
    rewrite bind_ret_l. repeat f_equal. extensionality x. destruct x. auto. }
  { i. replace g with f; auto. extensionality o. eapply H. }
Qed.
Global Opaque _APC.





Section CANCEL.

  Context `{Σ: GRA.t}.


  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: Any.t -> itree (hAPCE +' Es) Any.t;
  }
  .

  (*** argument remains the same ***)
  (* Definition mk_simple (mn: string) {X: Type} (P: X -> Any_tgt -> Σ -> ord -> Prop) (Q: X -> Any_tgt -> Σ -> Prop): fspec. *)
  (*   econs. *)
  (*   { apply mn. } *)
  (*   { i. apply (P X0 X2 X3 H /\ X1↑ = X2). } *)
  (*   { i. apply (Q X0 X2 X3 /\ X1↑ = X2). } *)
  (* Unshelve. *)
  (*   apply (list val). *)
  (*   apply (val). *)
  (* Defined. *)
  Definition mk_simple {X: Type} (DPQ: X -> ord * (Any_tgt -> iProp) * (Any_tgt -> iProp)): fspec :=
    mk_fspec (fst ∘ fst ∘ DPQ)
             (fun x y a => (((snd ∘ fst ∘ DPQ) x a: iProp) ∧ ⌜y = a⌝)%I)
             (fun x z a => (((snd ∘ DPQ) x a: iProp) ∧ ⌜z = a⌝)%I)
  .

  Section INTERP.
  (* Variable stb: gname -> option fspec. *)
  (*** TODO: I wanted to use above definiton, but doing so makes defining ms_src hard ***)
  (*** We can fix this by making ModSemL.fnsems to a function, but doing so will change the type of
       ModSemL.add to predicate (t -> t -> t -> Prop), not function.
       - Maybe not. I thought one needed to check uniqueness of gname at the "add",
         but that might not be the case.
         We may define fnsems: string -> option (list val -> itree Es val).
         When adding two ms, it is pointwise addition, and addition of (option A) will yield None when both are Some.
 ***)
  (*** TODO: try above idea; if it fails, document it; and refactor below with alist ***)

  Variable stb: gname -> option fspec.

  Definition handle_hAPCE_src: hAPCE ~> itree Es :=
    fun _ '(hAPC) => Ret tt.

  Definition interp_hEs_src: itree hEs ~> itree Es :=
    interp (case_ handle_hAPCE_src trivial_Handler)
  .

  Definition body_to_src {X} (body: X -> itree hEs Any.t): X -> itree Es Any.t :=
    (@interp_hEs_src _) ∘ body
  .

  Definition fun_to_src (body: Any.t -> itree hEs Any.t): ( Any.t -> itree Es Any_src) :=
    (body_to_src body)
  .



  Definition handle_hAPCE_tgt: hAPCE ~> itree Es' :=
    fun _ '(hAPC) => APC.

  Definition handle_callE_hEs: callE ~> itree Es' :=
    fun _ '(Call fn arg) => trigger (hCall false fn arg).

  Definition interp_hEs_tgt: itree (hAPCE +' Es) ~> itree Es' :=
    interp (case_ (bif:=sum1) (handle_hAPCE_tgt)
                  (case_ (bif:=sum1) (handle_callE_hEs)
                         trivial_Handler)).


  Definition handle_hCallE_mid2: hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      match tbr with
      | true => tau;; trigger (Choose _)
      | false => trigger (Call fn varg_src)
      end
  .

  Definition interp_hCallE_mid2: itree Es' ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_mid2)
                  trivial_Handler)
  .

  Definition body_to_mid2 {X} (body: X -> itree (hCallE +' sE +' eventE) Any.t): X -> itree Es Any.t :=
    (@interp_hCallE_mid2 _) ∘ body
  .

  Definition fun_to_mid2 (body: Any.t -> itree hEs Any.t): (Any_src -> itree Es Any_src) :=
    body_to_mid2 ((@interp_hEs_tgt _) ∘ body)
  .


  Definition handle_hCallE_mid (ord_cur: ord): hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      tau;;
      f <- (stb fn)ǃ;; guarantee (tbr = true -> ~ (forall x, f.(measure) x = ord_top));;;
      ord_next <- (if tbr then o0 <- trigger (Choose _);; Ret (ord_pure o0) else Ret ord_top);;
      guarantee(ord_lt ord_next ord_cur);;;
      let varg_mid: Any_mid := Any.pair ord_next↑ varg_src in
      trigger (Call fn varg_mid)
  .

  Definition interp_hCallE_mid (ord_cur: ord): itree Es' ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_mid ord_cur)
                  ((fun T X => trigger X): _ ~> itree Es))
  .

  Definition body_to_mid (ord_cur: ord) {X} (body: X -> itree (hCallE +' sE +' eventE) Any.t): X -> itree Es Any.t :=
    fun varg_mid => interp_hCallE_mid ord_cur (body varg_mid)
  .

  Definition fun_to_mid (body: Any.t -> itree hEs Any.t): (Any_mid -> itree Es Any_src) :=
    fun ord_varg_src =>
      '(ord_cur, varg_src) <- (Any.split ord_varg_src)ǃ;; ord_cur <- ord_cur↓ǃ;;
      interp_hCallE_mid ord_cur (interp_hEs_tgt
                                   (match ord_cur with
                                    | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                                    | _ => body (varg_src)
                                    end)).

  Definition handle_hCallE_tgt (ord_cur: ord): hCallE ~> stateT (Σ) (itree Es) :=
    fun _ '(hCall tbr fn varg_src) 'ctx =>
      f <- (stb fn)ǃ;;
      HoareCall tbr ord_cur f fn varg_src ctx
  .

  Definition handle_sE_tgt: sE ~> itree Es :=
      (fun _ e =>
         match e with
         | SUpdate run => pupdate run
         end).

  Definition interp_hCallE_tgt (ord_cur: ord): itree Es' ~> stateT Σ (itree Es) :=
    interp_state (case_ (bif:=sum1) (handle_hCallE_tgt ord_cur)
                        (case_ (bif:=sum1)
                               ((fun T X s => x <- handle_sE_tgt X;; Ret (s, x)): _ ~> stateT Σ (itree Es))
                               ((fun T X s => x <- trigger X;; Ret (s, x)): _ ~> stateT Σ (itree Es))))
  .

  Definition body_to_tgt (ord_cur: ord)
             {X} (body: X -> itree (hCallE +' sE +' eventE) Any_src): X -> stateT Σ (itree Es) Any_src :=
    (@interp_hCallE_tgt ord_cur _) ∘ body.


  Definition HoareFun
             {X: Type}
             (D: X -> ord)
             (P: X -> Any.t -> Any_tgt -> iProp)
             (Q: X -> Any.t -> Any_tgt -> iProp)
             (body: Any.t -> itree hEs Any.t): Any_tgt -> itree Es Any_tgt := fun varg_tgt =>
    x <- trigger (Take X);;
    '(ctx, varg_src) <- (ASSUME (P x) varg_tgt ε);;

    let ord_cur := D x in
    '(ctx, vret_src) <- interp_hCallE_tgt
                          ord_cur
                          (interp_hEs_tgt
                             (match ord_cur with
                              | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                              | _ => body (varg_src)
                              end)) ctx;;

    '(_, vret_tgt) <- (ASSERT (Q x) vret_src ctx);;
    Ret vret_tgt
  .

  Definition fun_to_tgt (sb: fspecbody): (Any_tgt -> itree Es Any_tgt) :=
    let fs: fspec := sb.(fsb_fspec) in
    (HoareFun (fs.(measure)) (fs.(precond)) (fs.(postcond)) (sb.(fsb_body)))
  .

(*** NOTE:
body can execute eventE events.
Notably, this implies it can also execute UB.
With this flexibility, the client code can naturally be included in our "type-checking" framework.
Also, note that body cannot execute "rE" on its own. This is intended.

NOTE: we can allow normal "callE" in the body too, but we need to ensure that it does not call "HoareFun".
If this feature is needed; we can extend it then. At the moment, I will only allow hCallE.
***)


  Definition HoareFunArg
             {X: Type}
             (P: X -> Any.t -> Any_tgt -> iProp):
    Any_tgt -> itree Es ((Σ) * (X * Any.t)) := fun varg_tgt =>
    x <- trigger (Take X);;
    '(ctx, varg_src) <- (ASSUME (P x) varg_tgt ε);;
    Ret (ctx, (x, varg_src))
  .

  Definition HoareFunRet
             {X: Type}
             (Q: X -> Any.t -> Any_tgt -> iProp):
    X -> ((Σ) * Any.t) -> itree Es Any_tgt := fun x '(ctx, vret_src) =>
    '(_, vret_tgt) <- (ASSERT (Q x) vret_src ctx);;
    Ret vret_tgt
  .

  Lemma HoareFun_parse
        {X: Type}
        (D: X -> ord)
        (P: X -> Any.t -> Any_tgt -> iProp)
        (Q: X -> Any.t -> Any_tgt -> iProp)
        (body: Any.t -> itree hEs Any.t)
        (varg_tgt: Any_tgt)
    :
      HoareFun D P Q body varg_tgt =
      '(ctx, (x, varg_src)) <- HoareFunArg P varg_tgt;;
      interp_hCallE_tgt (D x)
                        (interp_hEs_tgt
                           (match D x with
                            | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                            | _ => body varg_src
                            end)) ctx >>= (HoareFunRet Q x).
  Proof.
    unfold HoareFun, HoareFunArg, HoareFunRet. grind.
  Qed.

  End INTERP.



  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt md_tgt.(Mod.sk)).

  Variable sbtb: alist gname fspecbody.
  Let stb: alist gname fspec := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.














End CANCEL.

End PSEUDOTYPING.







Module SModSem.
Section SMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems: list (gname * fspecbody);
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  Definition transl (tr: fspecbody -> (Any.t -> itree Es Any.t)) (mst: t -> Any.t) (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, sb) => (fn, tr sb)) ms.(fnsems);
    ModSem.init_st := mst ms;
  |}
  .

  Definition to_src (ms: t): ModSem.t := transl (fun_to_src ∘ fsb_body) initial_st ms.
  Definition to_mid (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_mid stb ∘ fsb_body) initial_st ms.
  Definition to_mid2 (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_mid2 ∘ fsb_body) initial_st ms.
  Definition to_tgt (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_tgt stb) (fun ms => Any.pair ms.(initial_st) ms.(initial_mr)↑) ms.

  Definition main (mainpre: Any.t -> iProp) (mainbody: Any.t -> itree hEs Any.t): t := {|
      fnsems := [("main", (mk_specbody (mk_simple (fun (_: unit) => (ord_top, mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody))];
      initial_mr := ε;
      initial_st := tt↑;
    |}
  .

  Section ADD.

  Variable M1 M2: t.


  Definition emb_l : forall T, (hAPCE +' Es) T -> (hAPCE +' Es) T :=
    fun T E =>
    match E with
    | inr1 (inr1 (inl1 (SUpdate run))) => inr1 (inr1 (inl1 (SUpdate (ModSem.run_l run))))
    | _ => E
    end
  .

  Definition emb_r : forall T, (hAPCE +' Es) T -> (hAPCE +' Es) T :=
    fun T E =>
    match E with
    | inr1 (inr1 (inl1 (SUpdate run))) => inr1 (inr1 (inl1 (SUpdate (ModSem.run_r run))))
    | _ => E
    end
  .

  (* Definition trans_l f: (Any.t -> itree _ Any.t) :=
    (fun args => translate emb_l (f args)).

  Definition trans_r f: (Any.t -> itree _ Any.t) :=
    (fun args => translate emb_r (f args)). *)



  Definition trans_fspecbody emb fsb : fspecbody :=
  {|
    fsb_fspec := fsb.(fsb_fspec);
    fsb_body := (fun args => translate emb (fsb.(fsb_body) args));
  |}.

  Definition trans_l '(fn, f): gname * fspecbody :=
    (fn, (trans_fspecbody emb_l) f).

  Definition trans_r '(fn, f) : gname * fspecbody :=
    (fn, (trans_fspecbody emb_r) f).



  Definition add_fnsems : alist gname fspecbody :=
    (List.map trans_l M1.(fnsems)) ++ (List.map trans_r M2.(fnsems)).

  Definition add: t :=
  {|
    fnsems := add_fnsems;
    initial_mr := initial_mr M1; 
    (* initial_mr := fun n => URA._add (initial_mr M1 n) (initial_mr M2 n);  *)
    (* How do you add resource properly? *)
    initial_st := Any.pair (initial_st M1) (initial_st M2);
  |}.

  End ADD.
End SMODSEM.
End SModSem.



Module SMod.
Section SMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> SModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl (tr: Sk.t -> fspecbody -> ( Any.t -> itree Es Any.t)) (mst: SModSem.t -> Any.t) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => SModSem.transl (tr sk) mst (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  .

  Definition to_src (md: t): Mod.t := transl (fun _ => fun_to_src ∘ fsb_body) SModSem.initial_st md.
  Definition to_mid (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ => fun_to_mid stb ∘ fsb_body) SModSem.initial_st md.
  Definition to_mid2 (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ => fun_to_mid2 ∘ fsb_body) SModSem.initial_st md.
  Definition to_tgt (stb: Sk.t -> gname -> option fspec) (md: t): Mod.t :=
    transl (fun sk => fun_to_tgt (stb sk)) (fun ms => Any.pair ms.(SModSem.initial_st) ms.(SModSem.initial_mr)↑) md.

    



  Definition get_stb (md: t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd fsb_fspec) (SModSem.fnsems (get_modsem md sk)).

  Definition get_sk (md: t): Sk.t :=
    Sk.sort (Sk.add Sk.unit (sk md)).

  Definition get_init_mr (md: t): Sk.t -> Σ :=
    fun sk => (SModSem.initial_mr (get_modsem md sk)).


    

  (* Definition transl (tr: SModSem.t -> ModSem.t) (md: t): Mod.t := {| *)
  (*   Mod.get_modsem := (SModSem.transl tr) ∘ md.(get_modsem); *)
  (*   Mod.sk := md.(sk); *)
  (* |} *)
  (* . *)

  (* Definition to_src (md: t): Mod.t := transl SModSem.to_src md. *)
  (* Definition to_mid (md: t): Mod.t := transl SModSem.to_mid md. *)
  (* Definition to_tgt (stb: list (gname * fspec)) (md: t): Mod.t := transl (SModSem.to_tgt stb) md. *)
  Lemma to_src_comm: forall sk smd,
      (SModSem.to_src) (get_modsem smd sk) = (to_src smd).(Mod.get_modsem) sk.
  Proof. refl. Qed.
  Lemma to_mid_comm: forall sk stb smd,
      (SModSem.to_mid stb) (get_modsem smd sk) = (to_mid stb smd).(Mod.get_modsem) sk.
  Proof. refl. Qed.
  Lemma to_tgt_comm: forall sk stb smd,
      (SModSem.to_tgt (stb sk)) (get_modsem smd sk) = (to_tgt stb smd).(Mod.get_modsem) sk.
  Proof. refl. Qed.


  Section ADD.
    Definition add (md0 md1 : t) : t := {|
      get_modsem := fun sk =>
                        SModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
      sk := Sk.add md0.(sk) md1.(sk);
    |}.

    (* Definition empty: t := {|
      get_modsem := fun _ => SModSem.mk ε tt↑ [];
      sk := Sk.unit;
    |}. *)


    (* Fixpoint add_list (xs: list t): t :=
      match xs with
      | [] => empty
      | x::[] => x
      | x::l => add x (add_list l)
      end. *)


  End ADD.







  (* Definition l_bind A B (x: list A) (f: A -> list B): list B := List.flat_map f x. *)
  (* Definition l_ret A (a: A): list A := [a]. *)

  Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Lemma unconcat
        A (xs: list A)
    :
      List.concat (List.map (fun x => [x]) xs) = xs
  .
  Proof.
    induction xs; ii; ss. f_equal; ss.
  Qed.

  Lemma red_do_ret A B (xs: list A) (f: A -> B)
    :
      (do x <- xs; ret (f x)) = List.map f xs
  .
  Proof.
    rewrite flat_map_concat_map.
    erewrite <- List.map_map with (f:=f) (g:=ret).
    rewrite unconcat. ss.
  Qed.

  Lemma red_do_ret2 A0 A1 B (xs: list (A0 * A1)) (f: A0 -> A1 -> B)
    :
      (do '(x0, x1) <- xs; ret (f x0 x1)) = List.map (fun '(x0, x1) => f x0 x1) xs
  .
  Proof.
    induction xs; ss. rewrite IHxs. destruct a; ss.
  Qed.












  Local Opaque Mod.add_list.

  Lemma transl_sk
        tr mr md
    :
      <<SK: Mod.sk (transl tr mr md) = Sk.add Sk.unit (sk md)>>
  .
  Proof. ss. Qed.

  Lemma transl_sk_stable
        tr0 tr1 mr0 mr1 md
    :
      Mod.sk (transl tr0 mr0 md) =
      Mod.sk (transl tr1 mr1 md)
  .
  Proof. rewrite ! transl_sk. ss. Qed.

  Definition load_fnsems (sk: Sk.t) (md: t) (tr0: fspecbody -> Any.t -> itree Es Any.t) :=
    let ms := (get_modsem md sk) in
      (do '(fn, fsb) <- ms.(SModSem.fnsems);
       let fsem := tr0 fsb in
       ret (fn, fsem))
  .

  Lemma transl_fnsems_aux
        tr0 mr0 md
        (sk: Sk.t)
    :
      (ModSem.fnsems (Mod.get_modsem (transl tr0 mr0 md) sk)) =
      (load_fnsems sk md (tr0 sk))
  .
  Proof.
    unfold load_fnsems. cbn.
    rewrite flat_map_concat_map.
    replace (fun _x: string * fspecbody => let (fn, fsb) := _x in [(fn, tr0 sk fsb)]) with
        (ret ∘ (fun _x: string * fspecbody => let (fn, fsb) := _x in (fn, tr0 sk fsb)));
      cycle 1.
    { apply func_ext. i. des_ifs. }
    erewrite <- List.map_map with (g:=ret).
    rewrite unconcat.
    apply map_ext. ii. des_ifs.
  Qed.

  Lemma transl_fnsems
        tr0 mr0 md
    :
      (ModSem.fnsems (Mod.enclose (transl tr0 mr0 md))) =
      (load_fnsems (Sk.sort (Sk.add Sk.unit (sk md))) md (tr0 (Sk.sort (Sk.add Sk.unit (sk md)))))
  .
  Proof.
    unfold Mod.enclose.
    rewrite transl_fnsems_aux. f_equal.
  Qed.

  Lemma flat_map_assoc
        A B C
        (f: A -> list B)
        (g: B -> list C)
        (xs: list A)
    :
      (do y <- (do x <- xs; f x); g y) =
      (do x <- xs; do y <- (f x); g y)
  .
  Proof.
    induction xs; ii; ss.
    rewrite ! flat_map_concat_map in *. rewrite ! map_app. rewrite ! concat_app. f_equal; ss.
  Qed.

  Lemma transl_fnsems_stable
        tr0 tr1 mr0 mr1 md
    :
      List.map fst (Mod.enclose (transl tr0 mr0 md)).(ModSem.fnsems) =
      List.map fst (Mod.enclose (transl tr1 mr1 md)).(ModSem.fnsems)
  .
  Proof.
    rewrite ! transl_fnsems.
    unfold load_fnsems.
    rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i.
    des_ifs.
  Qed.




  Definition load_init_st {A} (sk: Sk.t) (md: t) (mr0: SModSem.t -> A): A :=
    let ms := (get_modsem md sk) in
    mr0 ms
  .

  Let transl_init_st_aux
        tr0 mr0 md
        (sk: Sk.t)
    :
      (ModSem.init_st (Mod.get_modsem (transl tr0 mr0 md) sk)) =
      (load_init_st sk md mr0)
  .
  Proof. ss. Qed.

  Lemma transl_init_st
        tr0 mr0 md
    :
      (ModSem.init_st (Mod.enclose ((transl tr0 mr0 md)))) =
      (load_init_st (Sk.sort (Sk.add Sk.unit (sk md))) md mr0)
  .
  Proof.
    unfold Mod.enclose.
    rewrite transl_init_st_aux. f_equal.
  Qed.

  Definition main (mainpre: Any.t -> iProp) (mainbody: Any.t -> itree hEs Any.t): t := {|
    get_modsem := fun _ => (SModSem.main mainpre mainbody);
    sk := Sk.unit;
  |}
  .

End SMOD.
End SMod.















  Hint Resolve Ord.lt_le_lt Ord.le_lt_lt OrdArith.lt_add_r OrdArith.le_add_l
       OrdArith.le_add_r Ord.lt_le
       Ord.lt_S
       Ord.S_lt
       Ord.S_supremum
       Ord.S_pos
    : ord.
  Hint Resolve Ord.le_trans Ord.lt_trans: ord_trans.
  Hint Resolve OrdArith.add_base_l OrdArith.add_base_r: ord_proj.

  Global Opaque interp_Es.






  Require Import Red.

  Ltac interp_red := erewrite interp_vis ||
                              erewrite interp_ret ||
                              erewrite interp_tau ||
                              erewrite interp_trigger ||
                              erewrite interp_bind.

  (* TODO: remove it *)
  Ltac interp_red2 := rewrite interp_vis ||
                              rewrite interp_ret ||
                              rewrite interp_tau ||
                              rewrite interp_trigger ||
                              rewrite interp_bind.

  Ltac _red_itree f :=
    match goal with
    | [ |- ?itr >>= _ = _] =>
      match itr with
      | _ >>= _ =>
        instantiate (f:=_continue); apply bind_bind; fail
      | Tau _ =>
        instantiate (f:=_break); apply bind_tau; fail
      | Ret _ =>
        instantiate (f:=_continue); apply bind_ret_l; fail
      | _ =>
        fail
      end
    | _ => fail
    end.



Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_tgt_bind
      (R S: Type)
      (s : itree (hCallE +' sE +' eventE) R) (k : R -> itree (hCallE +' sE +' eventE) S)
      stb o ctx
  :
    (interp_hCallE_tgt stb o (s >>= k)) ctx
    =
    st <- interp_hCallE_tgt stb o s ctx;; interp_hCallE_tgt stb o (k st.2) st.1.
Proof.
  unfold interp_hCallE_tgt in *. eapply interp_state_bind.
Qed.

Lemma interp_tgt_tau stb o ctx
      (U: Type)
      (t : itree _ U)
  :
    (interp_hCallE_tgt stb o (Tau t) ctx)
    =
    (Tau (interp_hCallE_tgt stb o t ctx)).
Proof.
  unfold interp_hCallE_tgt in *. eapply interp_state_tau.
Qed.

Lemma interp_tgt_ret stb o ctx
      (U: Type)
      (t: U)
  :
    (interp_hCallE_tgt stb o (Ret t) ctx)
    =
    Ret (ctx, t).
Proof.
  unfold interp_hCallE_tgt in *. eapply interp_state_ret.
Qed.

Lemma interp_tgt_triggerp stb o ctx
      (R: Type)
      (i: sE R)
  :
    (interp_hCallE_tgt stb o (trigger i) ctx)
    =
    (handle_sE_tgt i >>= (fun r => tau;; Ret (ctx, r))).
Proof.
  unfold interp_hCallE_tgt. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_tgt_triggere stb o ctx
      (R: Type)
      (i: eventE R)
  :
    (interp_hCallE_tgt stb o (trigger i) ctx)
    =
    (trigger i >>= (fun r => tau;; Ret (ctx, r))).
Proof.
  unfold interp_hCallE_tgt. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_tgt_hcall stb o ctx
      (R: Type)
      (i: hCallE R)
  :
    (interp_hCallE_tgt stb o (trigger i) ctx)
    =
    ((handle_hCallE_tgt stb o i ctx) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_tgt in *. rewrite interp_state_trigger. cbn. auto.
Qed.

Lemma interp_tgt_triggerUB stb o ctx
      (R: Type)
  :
    (interp_hCallE_tgt stb o (triggerUB) ctx)
    =
    triggerUB (A:=Σ*R).
Proof.
  unfold interp_hCallE_tgt, triggerUB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_tgt_triggerNB stb o ctx
      (R: Type)
  :
    (interp_hCallE_tgt stb o (triggerNB) ctx)
    =
    triggerNB (A:=Σ*R).
Proof.
  unfold interp_hCallE_tgt, triggerNB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_tgt_unwrapU stb o ctx
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_tgt stb o (@unwrapU (hCallE +' sE +' eventE) _ _ i) ctx)
    =
    r <- (unwrapU i);; Ret (ctx, r).
Proof.
  unfold interp_hCallE_tgt, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_tgt_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_tgt_unwrapN stb o ctx
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_tgt stb o (@unwrapN (hCallE +' sE +' eventE) _ _ i) ctx)
    =
    r <- (unwrapN i);; Ret (ctx, r).
Proof.
  unfold interp_hCallE_tgt, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_tgt_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_tgt_assume stb o ctx
      P
  :
    (interp_hCallE_tgt stb o (assume P) ctx)
    =
    (assume P;;; tau;; Ret (ctx, tt))
.
Proof.
  unfold assume. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_guarantee stb o ctx
      P
  :
    (interp_hCallE_tgt stb o (guarantee P) ctx)
    =
    (guarantee P;;; tau;; Ret (ctx, tt)).
Proof.
  unfold guarantee. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_ext stb o ctx
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hCallE_tgt stb o itr0 ctx)
    =
    (interp_hCallE_tgt stb o itr1 ctx)
.
Proof. subst; et. Qed.

Global Program Instance interp_hCallE_tgt_rdb: red_database (mk_box (@interp_hCallE_tgt)) :=
  mk_rdb
    1
    (mk_box interp_tgt_bind)
    (mk_box interp_tgt_tau)
    (mk_box interp_tgt_ret)
    (mk_box interp_tgt_hcall)
    (mk_box interp_tgt_triggere)
    (mk_box interp_tgt_triggerp)
    (mk_box interp_tgt_triggerp)
    (mk_box interp_tgt_triggerUB)
    (mk_box interp_tgt_triggerNB)
    (mk_box interp_tgt_unwrapU)
    (mk_box interp_tgt_unwrapN)
    (mk_box interp_tgt_assume)
    (mk_box interp_tgt_guarantee)
    (mk_box interp_tgt_ext)
.

End AUX.



Section AUX.

Context `{Σ: GRA.t}.
Variable stb: gname -> option fspec.
(* itree reduction *)
Lemma interp_mid_bind
      (R S: Type)
      (s : itree (hCallE +' sE +' eventE) R) (k : R -> itree (hCallE +' sE +' eventE) S)
      o
  :
    (interp_hCallE_mid stb o (s >>= k))
    =
    ((interp_hCallE_mid stb o s) >>= (fun r => interp_hCallE_mid stb o (k r))).
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_tau o
      (U: Type)
      (t : itree _ U)
  :
    (interp_hCallE_mid stb o (Tau t))
    =
    (Tau (interp_hCallE_mid stb o t)).
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_ret o
      (U: Type)
      (t: U)
  :
    ((interp_hCallE_mid stb o (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_triggerp o
      (R: Type)
      (i: sE R)
  :
    (interp_hCallE_mid stb o (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_triggere o
      (R: Type)
      (i: eventE R)
  :
    (interp_hCallE_mid stb o (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_hcall o
      (R: Type)
      (i: hCallE R)
  :
    (interp_hCallE_mid stb o (trigger i))
    =
    ((handle_hCallE_mid stb o i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_triggerUB o
      (R: Type)
  :
    (interp_hCallE_mid stb o (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hCallE_mid, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid_triggerNB o
      (R: Type)
  :
    (interp_hCallE_mid stb o (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hCallE_mid, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid_unwrapU o
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid stb o (@unwrapU (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hCallE_mid, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_mid_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_mid_unwrapN o
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid stb o (@unwrapN (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hCallE_mid, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_mid_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_mid_assume o
      P
  :
    (interp_hCallE_mid stb o (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_mid_bind. rewrite interp_mid_triggere. grind. eapply interp_mid_ret.
Qed.

Lemma interp_mid_guarantee o
      P
  :
    (interp_hCallE_mid stb o (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_mid_bind. rewrite interp_mid_triggere. grind. eapply interp_mid_ret.
Qed.

Lemma interp_mid_ext o
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hCallE_mid stb o itr0)
    =
    (interp_hCallE_mid stb o itr1)
.
Proof. subst; et. Qed.

End AUX.


Global Program Instance interp_hCallE_mid_rdb `{Σ: GRA.t}: red_database (mk_box (@interp_hCallE_mid)) :=
  mk_rdb
    0
    (mk_box interp_mid_bind)
    (mk_box interp_mid_tau)
    (mk_box interp_mid_ret)
    (mk_box interp_mid_hcall)
    (mk_box interp_mid_triggere)
    (mk_box interp_mid_triggerp)
    (mk_box interp_mid_triggerp)
    (mk_box interp_mid_triggerUB)
    (mk_box interp_mid_triggerNB)
    (mk_box interp_mid_unwrapU)
    (mk_box interp_mid_unwrapN)
    (mk_box interp_mid_assume)
    (mk_box interp_mid_guarantee)
    (mk_box interp_mid_ext)
.

Section AUX.

Context `{Σ: GRA.t}.
Variable stb: gname -> option fspec.
(* itree reduction *)
Lemma interp_mid2_bind
      (R S: Type)
      (s : itree (hCallE +' sE +' eventE) R) (k : R -> itree (hCallE +' sE +' eventE) S)
  :
    (interp_hCallE_mid2 (s >>= k))
    =
    ((interp_hCallE_mid2 s) >>= (fun r => interp_hCallE_mid2 (k r))).
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_tau
      (U: Type)
      (t : itree _ U)
  :
    (interp_hCallE_mid2 (Tau t))
    =
    (Tau (interp_hCallE_mid2 t)).
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_ret
      (U: Type)
      (t: U)
  :
    ((interp_hCallE_mid2 (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_triggerp
      (R: Type)
      (i: sE R)
  :
    (interp_hCallE_mid2 (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_triggere
      (R: Type)
      (i: eventE R)
  :
    (interp_hCallE_mid2 (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_hcall
      (R: Type)
      (i: hCallE R)
  :
    (interp_hCallE_mid2 (trigger i))
    =
    ((handle_hCallE_mid2 i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_triggerUB
      (R: Type)
  :
    (interp_hCallE_mid2 (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hCallE_mid2, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid2_triggerNB
      (R: Type)
  :
    (interp_hCallE_mid2 (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hCallE_mid2, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid2_unwrapU
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid2 (@unwrapU (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hCallE_mid2, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_mid2_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid2_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_mid2_unwrapN
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid2 (@unwrapN (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hCallE_mid2, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_mid2_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid2_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_mid2_assume
      P
  :
    (interp_hCallE_mid2 (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_mid2_bind. rewrite interp_mid2_triggere. grind. eapply interp_mid2_ret.
Qed.

Lemma interp_mid2_guarantee
      P
  :
    (interp_hCallE_mid2 (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_mid2_bind. rewrite interp_mid2_triggere. grind. eapply interp_mid2_ret.
Qed.

Lemma interp_mid2_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hCallE_mid2 itr0)
    =
    (interp_hCallE_mid2 itr1)
.
Proof. subst; et. Qed.

End AUX.


Global Program Instance interp_hCallE_mid2_rdb `{Σ: GRA.t}: red_database (mk_box (@interp_hCallE_mid2)) :=
  mk_rdb
    0
    (mk_box interp_mid2_bind)
    (mk_box interp_mid2_tau)
    (mk_box interp_mid2_ret)
    (mk_box interp_mid2_hcall)
    (mk_box interp_mid2_triggere)
    (mk_box interp_mid2_triggerp)
    (mk_box interp_mid2_triggerp)
    (mk_box interp_mid2_triggerUB)
    (mk_box interp_mid2_triggerNB)
    (mk_box interp_mid2_unwrapU)
    (mk_box interp_mid2_unwrapN)
    (mk_box interp_mid2_assume)
    (mk_box interp_mid2_guarantee)
    (mk_box interp_mid2_ext)
.



Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_src_bind
      (R S: Type)
      (s : itree hEs R) (k : R -> itree hEs S)
  :
    (interp_hEs_src (s >>= k))
    =
    ((interp_hEs_src s) >>= (fun r => interp_hEs_src (k r))).
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_tau
      (U: Type)
      (t : itree _ U)
  :
    (interp_hEs_src (Tau t))
    =
    (Tau (interp_hEs_src t)).
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_ret
      (U: Type)
      (t: U)
  :
    ((interp_hEs_src (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_triggerp
      (R: Type)
      (i: sE R)
  :
    (interp_hEs_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggere
      (R: Type)
      (i: eventE R)
  :
    (interp_hEs_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_call
      (R: Type)
      (i: callE R)
  :
    (interp_hEs_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_hapc
      (R: Type)
      (i: hAPCE R)
  :
    (interp_hEs_src (trigger i))
    =
    ((handle_hAPCE_src i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggerUB
      (R: Type)
  :
    (interp_hEs_src (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hEs_src, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_triggerNB
      (R: Type)
  :
    (interp_hEs_src (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hEs_src, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_unwrapU
      (R: Type)
      (i: option R)
  :
    (interp_hEs_src (@unwrapU hEs _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hEs_src, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_src_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_src_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_src_unwrapN
      (R: Type)
      (i: option R)
  :
    (interp_hEs_src (@unwrapN hEs _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hEs_src, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_src_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_src_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_src_assume
      P
  :
    (interp_hEs_src (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_guarantee
      P
  :
    (interp_hEs_src (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hEs_src itr0)
    =
    (interp_hEs_src itr1)
.
Proof. subst; et. Qed.

Global Program Instance interp_hEs_src_rdb: red_database (mk_box (@interp_hEs_src)) :=
  mk_rdb
    0
    (mk_box interp_src_bind)
    (mk_box interp_src_tau)
    (mk_box interp_src_ret)
    (mk_box interp_src_call)
    (mk_box interp_src_triggere)
    (mk_box interp_src_triggerp)
    (mk_box interp_src_hapc)
    (mk_box interp_src_triggerUB)
    (mk_box interp_src_triggerNB)
    (mk_box interp_src_unwrapU)
    (mk_box interp_src_unwrapN)
    (mk_box interp_src_assume)
    (mk_box interp_src_guarantee)
    (mk_box interp_src_ext)
.

End AUX.


Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_hEs_tgt_bind
      (R S: Type)
      (s : itree hEs R) (k : R -> itree hEs S)
  :
    (interp_hEs_tgt (s >>= k))
    =
    ((interp_hEs_tgt s) >>= (fun r => interp_hEs_tgt (k r))).
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_tau
      (U: Type)
      (t : itree _ U)
  :
    (interp_hEs_tgt (Tau t))
    =
    (Tau (interp_hEs_tgt t)).
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_ret
      (U: Type)
      (t: U)
  :
    ((interp_hEs_tgt (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_triggerp
      (R: Type)
      (i: sE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_triggere
      (R: Type)
      (i: eventE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_call
      (R: Type)
      (i: callE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    (handle_callE_hEs i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_hapc
      (R: Type)
      (i: hAPCE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    ((handle_hAPCE_tgt i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_triggerUB
      (R: Type)
  :
    (interp_hEs_tgt (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hEs_tgt, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_hEs_tgt_triggerNB
      (R: Type)
  :
    (interp_hEs_tgt (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hEs_tgt, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_hEs_tgt_unwrapU
      (R: Type)
      (i: option R)
  :
    (interp_hEs_tgt (@unwrapU hEs _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hEs_tgt, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_hEs_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_hEs_tgt_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_hEs_tgt_unwrapN
      (R: Type)
      (i: option R)
  :
    (interp_hEs_tgt (@unwrapN hEs _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hEs_tgt, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_hEs_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_hEs_tgt_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_hEs_tgt_assume
      P
  :
    (interp_hEs_tgt (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret.
Qed.

Lemma interp_hEs_tgt_guarantee
      P
  :
    (interp_hEs_tgt (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret.
Qed.

Lemma interp_hEs_tgt_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hEs_tgt itr0)
    =
    (interp_hEs_tgt itr1)
.
Proof. subst; et. Qed.

Global Program Instance interp_hEs_tgt_rdb: red_database (mk_box (@interp_hEs_tgt)) :=
  mk_rdb
    0
    (mk_box interp_hEs_tgt_bind)
    (mk_box interp_hEs_tgt_tau)
    (mk_box interp_hEs_tgt_ret)
    (mk_box interp_hEs_tgt_call)
    (mk_box interp_hEs_tgt_triggere)
    (mk_box interp_hEs_tgt_triggerp)
    (mk_box interp_hEs_tgt_hapc)
    (mk_box interp_hEs_tgt_triggerUB)
    (mk_box interp_hEs_tgt_triggerNB)
    (mk_box interp_hEs_tgt_unwrapU)
    (mk_box interp_hEs_tgt_unwrapN)
    (mk_box interp_hEs_tgt_assume)
    (mk_box interp_hEs_tgt_guarantee)
    (mk_box interp_hEs_tgt_ext)
.

End AUX.



(*** TODO: move to ITreeLib ***)
Lemma bind_eta E X Y itr0 itr1 (ktr: ktree E X Y): itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr. i; subst; refl. Qed.

Ltac ired_l := try (prw _red_gen 2 0).
Ltac ired_r := try (prw _red_gen 1 0).

Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).
  Ltac Esred :=
            try rewrite ! interp_Es_sE;
            try rewrite ! interp_Es_eventE; try rewrite ! interp_Es_callE;
            try rewrite ! interp_Es_triggerNB; try rewrite ! interp_Es_triggerUB (*** igo ***).
  (*** step and some post-processing ***)
  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso

    (*** assume/guarantee ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (gstep; econs; eauto; try (by eapply OrdArith.lt_from_nat; ss);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .
  Ltac steps := repeat (mred; try _step; des_ifs_safe).
  Ltac seal_left :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_src
    end.
  Ltac seal_right :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_tgt
    end.
  Ltac unseal_left :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (@Seal.sealing _ _ ?i_src) ?i_tgt ] => unseal i_src
    end.
  Ltac unseal_right :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src (@Seal.sealing _ _ ?i_tgt) ] => unseal i_tgt
    end.
  Ltac force_l := seal_right; _step; unseal_right.
  Ltac force_r := seal_left; _step; unseal_left.
  (* Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|]. *)

  From ExtLib Require Import
       Data.Map.FMapAList.

  Hint Resolve cpn3_wcompat: paco.
  Ltac init :=
    split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
    ginit; []; unfold alist_add, alist_remove; ss;
    unfold fun_to_tgt, cfunN; ss.


Notation Es' := (hCallE +' sE +' eventE).

Module IPCNotations.
  Notation ";;; t2" :=
    (ITree.bind (trigger hAPC) (fun _ => t2))
      (at level 63, t2 at next level, right associativity) : itree_scope.
  Notation "` x : t <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x : t => ;;; t2))
      (at level 62, t at next level, t1 at next level, x ident, right associativity) : itree_scope.
  Notation "x <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x => ;;; t2))
      (at level 62, t1 at next level, right associativity) : itree_scope.
  Notation "' p <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x_ => match x_ with p => ;;; t2 end))
      (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
End IPCNotations.

Export IPCNotations.
