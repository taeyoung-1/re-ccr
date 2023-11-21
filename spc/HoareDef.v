Require Import Coqlib AList.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import ModSemE.
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
    mk_fspec (meta:=unit) (fun _ => ord_top) (fun  _ argh argl => (⌜argh = argl⌝: iProp)%I)
             (fun  _ reth retl => (⌜reth = retl⌝: iProp)%I)
  .
End FSPEC.


Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.
  (* Variable S : Type. *)

  Definition mput {S} E `{sE (S * Σ)-< E} `{eventE -< E} (mr: Σ) : itree E unit :=
    '(mp, _)<- trigger (sGet id);;
    trigger (sPut (mp, mr))
  .

  Definition mget {S} E `{sE (S * Σ) -< E} `{eventE -< E}: itree E Σ :=
    '(_, mr) <- trigger (sGet id);; Ret mr
  .

  Definition pupdate {S} E `{sE (S * Σ)-<E} `{eventE -< E} {X} (run: S -> S * X) : itree E X :=
    trigger (SUpdate (fun '(x, mr) => ((fst (run x), mr), snd (run x))))
  .

  Definition ASSUME {S} (Cond: Any.t -> Any.t -> iProp) (valp: Any.t): stateT Σ (itree (Es (S * Σ))) Any.t :=
    fun fr =>
      '(cres, ctx) <- trigger (Take (Σ * Σ));;
      mr <- mget;;
      assume(URA.wf (cres ⋅ fr ⋅ ctx ⋅ mr));;;
      valv <- trigger (Take Any.t);;
      assume(Cond valv valp cres);;;
      Ret (ctx, valv)
  .

  Definition ASSERT {S} (Cond: Any.t -> Any.t -> iProp) (valv: Any.t): stateT Σ (itree (Es (S * Σ))) Any.t :=
    fun ctx =>
      '(cres, fr, mr) <- trigger (Choose (Σ * Σ * Σ));;
      mput mr;;;
      guarantee(URA.wf (cres ⋅ fr ⋅ ctx ⋅ mr));;;
      valp <- trigger (Choose Any.t);;
      guarantee(Cond valv valp cres);;;
      Ret (fr, valp)
  .


  Definition HoareCall
             {S}
             (tbr: bool)
             (ord_cur: ord)
             (fsp: fspec):
    gname -> Any.t -> stateT (Σ) (itree (Es (S * Σ))) Any.t :=
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

(* Variable S: Type. *)
Section APC.
Context `{Σ: GRA.t}.

Variable S: Type. 

Variant hCallE: Type -> Type :=
| hCall (tbr: bool) (fn: gname) (varg_src: Any_src): hCallE Any_src
(*** tbr == to be removed ***)
.

Variant hAPCE: Type -> Type :=
| hAPC: hAPCE unit
. 


(* (S * Σ) *)

Definition Es' := (hCallE +' sE S +' eventE).

Definition hEs := (hAPCE +' (Es S)).

Definition hcall {X Y} (fn: gname) (varg: X): itree (hCallE +' (sE S) +' eventE) Y :=
  vret <- trigger (hCall false fn varg↑);; vret <- vret↓ǃ;; Ret vret.

Program Fixpoint _APC (at_most: Ord.t) {wf Ord.lt at_most}: itree (Es') unit :=
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
End APC.
Global Opaque _APC.





Section CANCEL.

  Context `{Σ: GRA.t}.
  Variable S: Type.

  Record fspecbody : Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: Any.t -> itree (hAPCE +' (Es S)) Any.t;
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
             (fun  x y a => (((snd ∘ fst ∘ DPQ) x a: iProp) ∧ ⌜y = a⌝)%I)
             (fun  x z a => (((snd ∘ DPQ) x a: iProp) ∧ ⌜z = a⌝)%I)
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

  Definition handle_hAPCE_src: hAPCE ~> itree (Es S) :=
    fun _ '(hAPC) => Ret tt.

  Definition interp_hEs_src: itree (hEs S) ~> itree (Es S) :=
    interp (case_ handle_hAPCE_src trivial_Handler)
  .

  Definition body_to_src {X} (body: X -> itree (hEs S) Any.t): X -> itree (Es S) Any.t :=
    (@interp_hEs_src _) ∘ body
  .

  Definition fun_to_src (body: Any.t -> itree (hEs S) Any.t): ( Any.t -> itree (Es S) Any_src) :=
    (body_to_src body)
  .



  Definition handle_hAPCE_tgt : hAPCE ~> itree (Es' S) :=
    fun _ '(hAPC) => APC S.

  Definition handle_callE_hEs: callE ~> itree (Es' S) :=
    fun _ '(Call fn arg) => trigger (hCall false fn arg).

  Definition interp_hEs_tgt: itree (hAPCE +' (Es S)) ~> itree (Es' S) :=
    interp (case_ (bif:=sum1) (handle_hAPCE_tgt)
                  (case_ (bif:=sum1) (handle_callE_hEs)
                         trivial_Handler)).


  Definition handle_hCallE_mid2: hCallE ~> itree (Es S) :=
    fun _ '(hCall tbr fn varg_src) =>
      match tbr with
      | true => tau;; trigger (Choose _)
      | false => trigger (Call fn varg_src)
      end
  .

  Definition interp_hCallE_mid2: itree (Es' S) ~> itree (Es S) :=
    interp (case_ (bif:=sum1) (handle_hCallE_mid2)
                  trivial_Handler)
  .

  Definition body_to_mid2 {X} (body: X -> itree (hCallE +' (sE S) +' eventE) Any.t): X -> itree (Es S) Any.t :=
    (@interp_hCallE_mid2 _) ∘ body
  .

  Definition fun_to_mid2 (body: Any.t -> itree (hEs S) Any.t): ( Any_src -> itree (Es S) Any_src) :=
    body_to_mid2 ((@interp_hEs_tgt _) ∘ body)
  .


  Definition handle_hCallE_mid (ord_cur: ord): hCallE ~> itree (Es S) :=
    fun _ '(hCall tbr fn varg_src) =>
      tau;;
      f <- (stb fn)ǃ;; guarantee (tbr = true -> ~ (forall x, f.(measure) x = ord_top));;;
      ord_next <- (if tbr then o0 <- trigger (Choose _);; Ret (ord_pure o0) else Ret ord_top);;
      guarantee(ord_lt ord_next ord_cur);;;
      let varg_mid: Any_mid := Any.pair ord_next↑ varg_src in
      trigger (Call fn varg_mid)
  .

  Definition interp_hCallE_mid (ord_cur: ord): itree (Es' S) ~> itree (Es S) :=
    interp (case_ (bif:=sum1) (handle_hCallE_mid ord_cur)
                  ((fun T X => trigger X): _ ~> itree (Es S)))
  .

  Definition body_to_mid (ord_cur: ord) {X} (body: X -> itree (hCallE +' (sE S) +' eventE) Any.t): X -> itree (Es S) Any.t :=
    fun varg_mid => interp_hCallE_mid ord_cur (body varg_mid)
  .

  Definition fun_to_mid (body: Any.t -> itree (hEs S) Any.t): (Any_mid -> itree (Es S) Any_src) :=
    fun ord_varg_src =>
      '(ord_cur, varg_src) <- (Any.split ord_varg_src)ǃ;; ord_cur <- ord_cur↓ǃ;;
      interp_hCallE_mid ord_cur (interp_hEs_tgt
                                   (match ord_cur with
                                    | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                                    | _ => body (varg_src)
                                    end)).

  Definition handle_hCallE_tgt (ord_cur: ord): hCallE ~> stateT (Σ) (itree (Es (S * Σ))) :=
    fun _ '(hCall tbr fn varg_src) 'ctx =>
      f <- (stb fn)ǃ;;
      HoareCall tbr ord_cur f fn varg_src ctx
  .

  Definition handle_sE_tgt : (sE S) ~> itree (Es (S * Σ)) :=
    (* Eval unfold pput, pget in *)
      (fun _ e =>
         match e with
         (* | PPut st => pput st
         | PGet => pget *)
          | SUpdate run => pupdate run
         end).

  Definition interp_hCallE_tgt (ord_cur: ord): itree (Es' S) ~> stateT Σ (itree (Es (S * Σ)) ) :=
    interp_state (case_ (bif:=sum1) (handle_hCallE_tgt ord_cur)
                        (case_ (bif:=sum1)
                               ((fun T X s => x <- handle_sE_tgt X;; Ret (s, x)): _ ~> stateT Σ (itree (Es (S * Σ))))
                               ((fun T X s => x <- trigger X;; Ret (s, x)): _ ~> stateT Σ (itree (Es (S * Σ))))))
  .

  Definition body_to_tgt (ord_cur: ord)
             {X} (body: X -> itree (hCallE +' (sE S) +' eventE) Any_src): X -> stateT Σ (itree (Es (S * Σ))) Any_src :=
    (@interp_hCallE_tgt ord_cur _) ∘ body.


  Definition HoareFun
             {X: Type}
             (D: X -> ord)
             (P: X -> Any.t -> Any_tgt -> iProp)
             (Q: X -> Any.t -> Any_tgt -> iProp)
             (body: (Any.t) -> itree (hEs S) Any.t): Any_tgt -> itree (Es (S * Σ)) Any_tgt := fun varg_tgt =>
    x <- trigger (Take X);;
    '(ctx, varg_src) <- (ASSUME (P x) varg_tgt ε);;

    let ord_cur := D x in
    '(ctx, vret_src) <- interp_hCallE_tgt
                          ord_cur
                          (interp_hEs_tgt
                             (match ord_cur with
                              | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                              | _ => body varg_src
                              end)) ctx;;

    '(_, vret_tgt) <- (ASSERT (Q x) vret_src ctx);;
    Ret vret_tgt
  .
  

  Definition fun_to_tgt (sb: fspecbody): (Any_tgt -> itree (Es (S * Σ)) Any_tgt) :=
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
    Any_tgt -> itree (Es (S * Σ)) ((Σ) * (X * Any.t)) := fun varg_tgt =>
    x <- trigger (Take X);;
    '(ctx, varg_src) <- (ASSUME (P x) varg_tgt ε);;
    Ret (ctx, (x, varg_src))
  .

  Definition HoareFunRet
             {X: Type}
             (Q: X -> Any.t -> Any_tgt -> iProp):
    X -> ((Σ) * Any.t) -> itree (Es (S * Σ)) Any_tgt := fun x '(ctx, vret_src) =>
    '(_, vret_tgt) <- (ASSERT (Q x) vret_src ctx);;
    Ret vret_tgt
  .

  Lemma HoareFun_parse
        {X: Type}
        (D: X -> ord)
        (P: X -> Any.t -> Any_tgt -> iProp)
        (Q: X -> Any.t -> Any_tgt -> iProp)
        (body: (Any.t) -> itree (hEs S) Any.t)
        (varg_tgt: Any_tgt)
    :
      HoareFun D P Q body varg_tgt =
      '(ctx, (x, varg_src)) <- HoareFunArg P varg_tgt;;
      interp_hCallE_tgt (D x)
                        (interp_hEs_tgt
                           (match D x with
                            | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                            | _ => body (varg_src)
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
    state: Type;
    initial_mr: Σ;
    initial_st: state;
    fnsems: gname -> option (fspecbody state)
  }
  .

  (* Notation lift ms := ( fspecbody (state ms) -> (Any.t -> itree (Es (state ms)) Any.t) ).

  Definition a := fun (ms: t) => lift ms. *)

  (* Definition get_tr (ms: t): (fspecbody ms.(state) -> (Any.t -> itree (Es ms.(state)) Any.t) ) := 
    fun fsb => fun_to_src (fsb_body fsb). *)


  Definition transl (ms: t) (tr: fspecbody ms.(state) -> (Any.t -> itree (Es ms.(state)) Any.t) ) : ModSem.t := {|
    ModSem.state := state ms;
    ModSem.init_st := initial_st ms;
    ModSem.fnsems := (fun fn => match (fnsems ms fn) with
                              | Some sb => Some (tr sb)
                              | _ => None
                              end
                              )
  |}
  .

  (* Definition transl (tr: forall S, fspecbody S -> (Any.t -> itree (Es (S)) Any.t) ) (ms: t) : ModSem.t := {|
    ModSem.state := state ms;
    ModSem.init_st := initial_st ms;
    ModSem.fnsems := (fun fn => match (fnsems ms fn) with
                              | Some sb => Some (tr (state ms) sb)
                              | _ => None
                              end
                              )
  |}
  . *)


  (* Definition real_transl ms (f) := transl ms (get_tr ms). *)

  Definition transl_tgt (ms: t) (tr: fspecbody (state ms) -> (Any.t -> itree (Es ((state ms) * Σ)) Any.t) ) : ModSem.t := {|
    ModSem.state := (state ms) * Σ;
    ModSem.init_st := (initial_st ms, initial_mr ms);
    ModSem.fnsems := (fun fn => match (fnsems ms fn) with
                              | Some sb => Some (tr sb)
                              | _ => None
                              end
                              )
  
  |}
  .

  (* Definition transl_tgt (tr: forall S, fspecbody S -> (Any.t -> itree (Es (S * Σ)) Any.t) )  (ms: t) : ModSem.t := {|
    ModSem.state := (state ms) * Σ;
    ModSem.init_st := (initial_st ms, initial_mr ms);
    ModSem.fnsems := (fun fn => match (fnsems ms fn) with
                              | Some sb => Some (tr (state ms) sb)
                              | _ => None
                              end
                              )
  
  |}
  . *)

  Definition to_src (ms: t): ModSem.t := transl ms (fun fsb => fun_to_src (fsb_body fsb)).
  Definition to_mid (stb: gname -> option fspec) (ms: t): ModSem.t := transl ms (fun fsb => fun_to_mid stb (fsb_body fsb)).
  Definition to_mid2 (stb: gname -> option fspec) (ms: t): ModSem.t := transl ms (fun fsb => fun_to_mid2 (fsb_body fsb)).
  Definition to_tgt (stb: gname -> option fspec) (ms: t): ModSem.t := transl_tgt ms (fun fsb => fun_to_tgt stb fsb).

  (* Definition to_src (ms: t): ModSem.t := transl (fun _ fsb => fun_to_src (fsb_body fsb)) ms.
  Definition to_mid (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun _ fsb => fun_to_mid stb (fsb_body fsb)) ms.
  Definition to_mid2 (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun _ fsb => fun_to_mid2 (fsb_body fsb)) ms.
  Definition to_tgt (stb: gname -> option fspec) (ms: t): ModSem.t := transl_tgt (fun _ fsb => fun_to_tgt stb fsb) ms. *)


  (* Definition to_src (ms: t): ModSem.t := transl (fun mn => fun_to_src ∘ fsb_body) initial_st ms. *)
  (* Definition to_mid (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun mn => fun_to_mid stb ∘ fsb_body) initial_st ms. *)
  (* Definition to_mid2 (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun mn => fun_to_mid2 ∘ fsb_body) initial_st ms. *)
  (* Definition to_tgt (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun mn => fun_to_tgt mn stb) (fun ms => Any.pair ms.(initial_st) ms.(initial_mr)↑) ms. *)

  Definition main (mainpre: Any.t -> iProp) (mainbody: (Any.t) -> itree (hEs unit) Any.t): t := {|
    state := unit;
    initial_mr := ε;
    initial_st := tt;
    fnsems := (fun fn => match fn with
                      | "main" => Some (mk_specbody (mk_simple (fun (_: unit) => (ord_top, mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody)
                      | _ => None
                      end
              )
    (* fnsems := [("main", (mk_specbody (mk_simple (fun (_: unit) => (ord_top, mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody))]; *)
    |}
  .

  (* Definition main (mainpre: Any.t -> iProp) (mainbody: (option mname * Any.t) -> itree hEs Any.t): t := {|
      fnsems := [("main", (mk_specbody (mk_simple (fun (_: unit) => (ord_top, mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody))];
      mn := "Main";
      initial_mr := ε;
      initial_st := tt↑;
    |}
  . *)

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

  (* (tr: Sk.t -> fspecbody (SModSem.state ((get_modsem md) _)) -> (Any.t -> itree (Es (SModSem.state ((get_modsem md) _))) Any.t)) *)

  Definition transl (md: t) tr: Mod.t := {|
    Mod.get_modsem := fun sk => SModSem.transl ((get_modsem md) sk) (tr sk);
    Mod.sk := md.(sk);
  |}
  .

  Definition transl_tgt (md: t) tr: Mod.t := {|
    Mod.get_modsem := fun sk => SModSem.transl_tgt ((get_modsem md) sk) (tr sk);
    Mod.sk := md.(sk);
  |}
  .

  (* Definition transl (tr: Sk.t -> mname -> fspecbody -> (option mname * Any.t -> itree Es Any.t)) (mst: SModSem.t -> Any.t) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => SModSem.transl (tr sk) mst (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  . *)

  Definition to_src (md: t): Mod.t := transl md (fun _ fsb => fun_to_src (fsb_body fsb)).
  Definition to_mid (stb: gname -> option fspec) (md:t) : Mod.t := transl md (fun _ fsb => fun_to_mid stb (fsb_body fsb)).
  Definition to_mid2 (stb: gname -> option fspec) (md:t) : Mod.t := transl md (fun _ fsb => fun_to_mid2 (fsb_body fsb)).
  Definition to_tgt (stb: Sk.t -> gname -> option fspec) (md: t): Mod.t :=
    transl_tgt md (fun sk => fun_to_tgt (stb sk)).

  (* Definition to_src (md: t): Mod.t := transl (fun _ _ => fun_to_src ∘ fsb_body) SModSem.initial_st md.
  Definition to_mid (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ _ => fun_to_mid stb ∘ fsb_body) SModSem.initial_st md.
  Definition to_mid2 (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ _ => fun_to_mid2 ∘ fsb_body) SModSem.initial_st md.
  Definition to_tgt (stb: Sk.t -> gname -> option fspec) (md: t): Mod.t :=
    transl (fun sk mn => fun_to_tgt mn (stb sk)) (fun ms => Any.pair ms.(SModSem.initial_st) ms.(SModSem.initial_mr)↑) md. *)



(* 
  (* How to specify the Type of fspecbody? *)
  Definition get_stb (mds: list t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd fsb_fspec ) (flat_map (SModSem.fnsems ∘ (flip get_modsem sk)) mds).

  Definition get_sk (mds: list t): Sk.t :=
    Sk.sort (fold_right Sk.add Sk.unit (List.map sk mds)).

  Definition get_initial_mrs (mds: list t): Sk.t -> Σ :=
    fun sk => fold_left (⋅) (List.map (SModSem.initial_mr ∘ (flip get_modsem sk)) mds) ε. *)


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







(* 


  Local Opaque Mod.add_list.

  Lemma transl_sk
        tr0 mr0 mds
    :
      <<SK: Mod.sk (Mod.add_list ((List.map transl mds))) = fold_right Sk.add Sk.unit (List.map sk mds)>>
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. ss. r. f_equal. ss.
  Qed.

  Lemma transl_sk_stable
        tr0 tr1 mr0 mr1 mds
    :
      ModL.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) =
      ModL.sk (Mod.add_list (List.map (transl tr1 mr1) mds))
  .
  Proof. rewrite ! transl_sk. ss. Qed.

  Definition load_fnsems (sk: Sk.t) (mds: list t) (tr0: mname -> fspecbody -> option mname * Any.t -> itree Es Any.t) :=
    do md <- mds;
    let ms := (get_modsem md sk) in
      (do '(fn, fsb) <- ms.(SModSem.fnsems);
       let fsem := tr0 ms.(SModSem.mn) fsb in
       ret (fn, transl_all (T:=_) ms.(SModSem.mn) ∘ fsem))
  .

  Let transl_fnsems_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSemL.fnsems (ModL.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_fnsems sk mds (tr0 sk))
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. cbn. f_equal; ss.
    rewrite ! List.map_map.

    rewrite flat_map_concat_map.
    replace (fun _x: string * fspecbody => let (fn, fsb) := _x in [(fn, transl_all (T:=_) (SModSem.mn (get_modsem a sk)) ∘ (tr0 sk (get_modsem a sk).(SModSem.mn) fsb))]) with
        (ret ∘ (fun _x: string * fspecbody => let (fn, fsb) := _x in (fn, transl_all (T:=_) (SModSem.mn (get_modsem a sk)) ∘ (tr0 sk (get_modsem a sk).(SModSem.mn) fsb))));
      cycle 1.
    { apply func_ext. i. des_ifs. }
    erewrite <- List.map_map with (g:=ret).
    rewrite unconcat.
    apply map_ext. ii. des_ifs.
  Qed.

  Lemma transl_fnsems
        tr0 mr0 mds
    :
      (ModSemL.fnsems (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_fnsems (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds (tr0 (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds)))))
  .
  Proof.
    unfold ModL.enclose.
    rewrite transl_fnsems_aux. do 2 f_equal. rewrite transl_sk. ss.
    rewrite transl_sk. auto.
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
        tr0 tr1 mr0 mr1 mds
    :
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSemL.fnsems) =
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSemL.fnsems)
  .
  Proof.
    rewrite ! transl_fnsems.
    unfold load_fnsems.
    rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i.
    des_ifs.
  Qed.




  Definition load_initial_mrs {A} (sk: Sk.t) (mds: list t) (mr0: SModSem.t -> A): list (string * A) :=
    do md <- mds;
    let ms := (get_modsem md sk) in
    ret (ms.(SModSem.mn), mr0 ms)
  .

  Let transl_initial_mrs_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_initial_mrs sk mds mr0)
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. cbn. f_equal; ss.
  Qed.

  Lemma transl_initial_mrs
        tr0 mr0 mds
    :
      (ModSemL.initial_mrs (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_initial_mrs (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds mr0)
  .
  Proof.
    unfold ModL.enclose.
    rewrite transl_initial_mrs_aux. do 2 f_equal. rewrite transl_sk. ss.
  Qed.

  Lemma transl_stable_mn
        tr0 tr1 mr0 mr1 mds
    :
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSemL.initial_mrs) =
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSemL.initial_mrs)
  .
  Proof.
    rewrite ! transl_initial_mrs. unfold load_initial_mrs. rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i. ss.
  Qed.

  Definition main (mainpre: Any.t -> iProp) (mainbody: (option mname * Any.t) -> itree hEs Any.t): t := {|
    get_modsem := fun _ => (SModSem.main mainpre mainbody);
    sk := Sk.unit;
  |}
  . *)

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
(* Variable S: Type. *)
(* itree reduction *)
Lemma interp_tgt_bind
      (S R T: Type)
      (s : itree (hCallE +' sE S +' eventE) R) (k : R -> itree (hCallE +' sE S +' eventE) T)
      stb o ctx
  :
    (interp_hCallE_tgt stb o (s >>= k)) ctx
    =
    st <- interp_hCallE_tgt stb o s ctx;; interp_hCallE_tgt stb o (k st.2) st.1.
Proof.
  unfold interp_hCallE_tgt in *. eapply interp_state_bind.
Qed.

Lemma interp_tgt_tau stb o ctx
      (S U: Type)
      (t : itree (Es' S) U)
  :
    (interp_hCallE_tgt stb o (Tau t) ctx)
    =
    (Tau (interp_hCallE_tgt stb o t ctx)).
Proof.
  unfold interp_hCallE_tgt in *. eapply interp_state_tau.
Qed.

Lemma interp_tgt_ret stb o ctx
      (S U: Type)
      (t: U)
      (* (r := {| _observe := @RetF (Es' S) _ _ t |}) *)
  :
    (interp_hCallE_tgt stb o (Ret t: itree (Es' S) U) ctx)
    =
    Ret (ctx, t).
Proof.
  unfold interp_hCallE_tgt in *. eapply interp_state_ret.
Qed.

Lemma interp_tgt_triggerp stb o ctx
      (S R: Type)
      (i: sE S R)
  :
    (interp_hCallE_tgt stb o (trigger i) ctx)
    =
    (handle_sE_tgt i >>= (fun r => tau;; Ret (ctx, r))).
Proof.
  unfold interp_hCallE_tgt. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_tgt_triggere stb o (ctx: Σ)
      (S R: Type)
      (i: eventE R)
      (* (t := ITree.trigger (@subevent eventE (Es' S) _ _ i)) *)
      (* (t' := ITree.trigger (@subevent eventE (Es (S * Σ)) _ _ i)) *)

  :
    (interp_hCallE_tgt stb o (trigger i: itree (Es' S) R) ctx)
    =
    (trigger i >>= (fun r => tau;; Ret (ctx, r))).
Proof. 
  unfold interp_hCallE_tgt. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_tgt_hcall stb o ctx
      (S R: Type)
      (i: hCallE R)
  :
    (interp_hCallE_tgt stb o (trigger i: itree (Es' S) R) ctx)
    =
    ((handle_hCallE_tgt S stb o i ctx) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_tgt in *. rewrite interp_state_trigger. cbn. auto.
Qed.

Lemma interp_tgt_triggerUB stb o ctx
      (S R: Type)
  :
    (interp_hCallE_tgt stb o (triggerUB: itree (Es' S) R) ctx)
    =
    triggerUB (A:=Σ*R).
Proof.
  unfold interp_hCallE_tgt, triggerUB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_tgt_triggerNB stb o ctx
      (S R: Type)
  :
    (interp_hCallE_tgt stb o (triggerNB: itree (Es' S) R) ctx)
    =
    triggerNB (A:=Σ*R).
Proof.
  unfold interp_hCallE_tgt, triggerNB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_tgt_unwrapU stb o ctx
      (S R: Type)
      (i: option R)
  :
    (interp_hCallE_tgt stb o (@unwrapU (hCallE +' (sE S) +' eventE) _ _ i) ctx)
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
      (S R: Type)
      (i: option R)
  :
    (interp_hCallE_tgt stb o (@unwrapN (hCallE +' (sE S) +' eventE) _ _ i) ctx)
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

Lemma interp_tgt_assume stb o ctx S
      P
  :
    (interp_hCallE_tgt stb o (assume P: itree (Es' S) _) ctx)
    =
    (assume P;;; tau;; Ret (ctx, tt))
.
Proof.
  unfold assume. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_guarantee stb o ctx S
      P
  :
    (interp_hCallE_tgt stb o (guarantee P: itree (Es' S) _) ctx)
    =
    (guarantee P;;; tau;; Ret (ctx, tt)).
Proof.
  unfold guarantee. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_ext stb o ctx S
      R (itr0 itr1: itree (Es' S) R)
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
(* Variable stb: gname -> option fspec. *)
(* Variable S: Type. *)

(* itree reduction *)
Lemma interp_mid_bind
      (S R T: Type) (stb: gname -> option fspec)
      (s : itree (hCallE +' (sE S) +' eventE) R) (k : R -> itree (hCallE +' (sE S) +' eventE) T)
      o
  :
    (interp_hCallE_mid stb o (s >>= k))
    =
    ((interp_hCallE_mid stb o s) >>= (fun r => interp_hCallE_mid stb o (k r))).
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_tau o
      (S U: Type) (stb: gname -> option fspec)
      (t : itree (Es' S) U)
  :
    (interp_hCallE_mid stb o (Tau t))
    =
    (Tau (interp_hCallE_mid stb o t)).
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_ret o
      (S U: Type) (stb: gname -> option fspec)
      (t: U)
  :
    ((interp_hCallE_mid stb o (Ret t: itree (Es' S) _)))
    =
    Ret t.
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_triggerp o
      (S R: Type) (stb: gname -> option fspec)
      (i: (sE S) R)
  :
    (interp_hCallE_mid stb o (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_triggere o
      (S R: Type) (stb: gname -> option fspec)
      (i: eventE R) 
  :
    (interp_hCallE_mid stb o (trigger i: itree (Es' S) _))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_hcall o
      (S R: Type) (stb: gname -> option fspec)
      (i: hCallE R)
  :
    (interp_hCallE_mid stb o (trigger i: itree (Es' S) _))
    =
    ((handle_hCallE_mid S stb o i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_triggerUB o
      (S R: Type) (stb: gname -> option fspec)
  :
    (interp_hCallE_mid stb o (triggerUB: itree (Es' S) _))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hCallE_mid, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid_triggerNB o
      (S R: Type) stb
  :
    (interp_hCallE_mid stb o (triggerNB: itree (Es' S) _))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hCallE_mid, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid_unwrapU o
      (S R: Type) stb
      (i: option R)
  :
    (interp_hCallE_mid stb o (@unwrapU (hCallE +' (sE S) +' eventE) _ _ i))
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
      (S R: Type) stb
      (i: option R)
  :
    (interp_hCallE_mid stb o (@unwrapN (hCallE +' (sE S) +' eventE) _ _ i))
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
      S P stb
  :
    (interp_hCallE_mid stb o (assume P: itree (Es' S) _))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_mid_bind. rewrite interp_mid_triggere. grind. eapply interp_mid_ret.
Qed.

Lemma interp_mid_guarantee o
      S P stb
  :
    (interp_hCallE_mid stb o (guarantee P: itree (Es' S) _))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_mid_bind. rewrite interp_mid_triggere. grind. eapply interp_mid_ret.
Qed.

Lemma interp_mid_ext o S stb
      R (itr0 itr1: itree (Es' S) R)
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
(* Variable (stb: gname -> option fspec). *)
(* Variable S: Type. *)
(* itree reduction *)
Lemma interp_mid2_bind
      (S R T: Type)
      (s : itree (hCallE +' (sE S) +' eventE) R) (k : R -> itree (hCallE +' (sE S) +' eventE) T)
  :
    (interp_hCallE_mid2 (s >>= k))
    =
    ((interp_hCallE_mid2 s) >>= (fun r => interp_hCallE_mid2 (k r))).
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_tau
      (S U: Type)
      (t : itree (Es' S) U)
  :
    (interp_hCallE_mid2 (Tau t))
    =
    (Tau (interp_hCallE_mid2 t)).
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_ret
      (S U: Type)
      (t: U)
  :
    ((interp_hCallE_mid2 (Ret t: itree (Es' S) _)))
    =
    Ret t.
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_triggerp
      (R S: Type)
      (i: (sE S) R)
  :
    (interp_hCallE_mid2 (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_triggere
      (S R: Type)
      (i: eventE R)
  :
    (interp_hCallE_mid2 (trigger i: itree (Es' S) _))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_hcall
      (S R: Type) 
      (i: hCallE R) 
  :
    (interp_hCallE_mid2 (trigger i: itree (Es' S) _))
    =
    ((handle_hCallE_mid2 S i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_triggerUB
      (S R: Type)
  :
    (interp_hCallE_mid2 (triggerUB: itree (Es' S) _))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hCallE_mid2, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid2_triggerNB
      (S R: Type)
  :
    (interp_hCallE_mid2 (triggerNB: itree (Es' S) _))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hCallE_mid2, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid2_unwrapU
      (S R: Type)
      (i: option R)
  :
    (interp_hCallE_mid2 (@unwrapU (hCallE +' (sE S) +' eventE) _ _ i))
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
      (S R: Type)
      (i: option R)
  :
    (interp_hCallE_mid2 (@unwrapN (hCallE +' (sE S) +' eventE) _ _ i))
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
      S P 
  :
    (interp_hCallE_mid2 (assume P: itree (Es' S) _))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_mid2_bind. rewrite interp_mid2_triggere. grind. eapply interp_mid2_ret.
Qed.

Lemma interp_mid2_guarantee
      S P
  :
    (interp_hCallE_mid2 (guarantee P: itree (Es' S) _))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_mid2_bind. rewrite interp_mid2_triggere. grind. eapply interp_mid2_ret.
Qed.

Lemma interp_mid2_ext 
      S R (itr0 itr1: itree (Es' S) R)
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
(* Variable S: Type. *)
(* itree reduction *)
Lemma interp_src_bind
      (S R T: Type)
      (s : itree (hEs S) R) (k : R -> itree (hEs S) T)
  :
    (interp_hEs_src (s >>= k))
    =
    ((interp_hEs_src s) >>= (fun r => interp_hEs_src (k r))).
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_tau
      (S U: Type)
      (t : itree (hEs S) U)
  :
    (interp_hEs_src (Tau t))
    =
    (Tau (interp_hEs_src t)).
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_ret
      (S U: Type)
      (t: U)
  :
    ((interp_hEs_src (Ret t: itree (hEs S) _)))
    =
    Ret t.
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_triggerp
      (S R: Type)
      (i: (sE S) R)
  :
    (interp_hEs_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggere
      (S R: Type)
      (i: eventE R)
  :
    (interp_hEs_src (trigger i: itree (hEs S) _))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_call
      (S R: Type)
      (i: callE R)
  :
    (interp_hEs_src (trigger i: itree (hEs S) _))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_hapc
      (S R: Type)
      (i: hAPCE R)
  :
    (interp_hEs_src (trigger i: itree (hEs S) _))
    =
    ((handle_hAPCE_src S i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggerUB
      (S R: Type)
  :
    (interp_hEs_src (triggerUB: itree (hEs S) _))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hEs_src, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_triggerNB
      (S R: Type)
  :
    (interp_hEs_src (triggerNB: itree (hEs S) _))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hEs_src, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_unwrapU
      (S R: Type)
      (i: option R)
  :
    (interp_hEs_src (@unwrapU (hEs S) _ _ i))
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
      (S R: Type)
      (i: option R)
  :
    (interp_hEs_src (@unwrapN (hEs S) _ _ i))
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
      S P
  :
    (interp_hEs_src (assume P: itree (hEs S) _))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_guarantee
      S P
  :
    (interp_hEs_src (guarantee P: itree (hEs S) _))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_ext
      S R (itr0 itr1: itree (hEs S) R)
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
(* Variable S: Type. *)
(* itree reduction *)
Lemma interp_hEs_tgt_bind
      (S R T: Type)
      (s : itree (hEs S) R) (k : R -> itree (hEs S) T)
  :
    (interp_hEs_tgt (s >>= k))
    =
    ((interp_hEs_tgt s) >>= (fun r => interp_hEs_tgt (k r))).
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_tau
      (S U: Type)
      (t : itree (hEs S) U)
  :
    (interp_hEs_tgt (Tau t))
    =
    (Tau (interp_hEs_tgt t)).
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_ret
      (S U: Type)
      (t: U)
  :
    ((interp_hEs_tgt (Ret t: itree (hEs S) _)))
    =
    Ret t.
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_triggerp
      (S R: Type)
      (i: (sE S) R)
  :
    (interp_hEs_tgt (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_triggere
      (S R: Type)
      (i: eventE R)
  :
    (interp_hEs_tgt (trigger i: itree (hEs S) _))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_call
      (S R: Type)
      (i: callE R)
  :
    (interp_hEs_tgt (trigger i: itree (hEs S) _))
    =
    (handle_callE_hEs S i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_hapc
      (S R: Type)
      (i: hAPCE R)
  :
    (interp_hEs_tgt (trigger i: itree (hEs S) _))
    =
    ((handle_hAPCE_tgt S i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_triggerUB
      (S R: Type)
  :
    (interp_hEs_tgt (triggerUB: itree (hEs S) _))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hEs_tgt, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_hEs_tgt_triggerNB
      (S R: Type)
  :
    (interp_hEs_tgt (triggerNB: itree (hEs S) _))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hEs_tgt, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_hEs_tgt_unwrapU
      (S R: Type)
      (i: option R)
  :
    (interp_hEs_tgt (@unwrapU (hEs S) _ _ i))
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
      (S R: Type)
      (i: option R)
  :
    (interp_hEs_tgt (@unwrapN (hEs S) _ _ i))
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
      S P
  :
    (interp_hEs_tgt (assume P: itree (hEs S) _))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret.
Qed.

Lemma interp_hEs_tgt_guarantee
      S P
  :
    (interp_hEs_tgt (guarantee P: itree (hEs S) _))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret.
Qed.

Lemma interp_hEs_tgt_ext
      S R (itr0 itr1: itree (hEs S) R)
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

