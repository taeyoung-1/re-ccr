Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.

(* Require Import lmHeader. *)

Set Implicit Arguments.

Section H.
  Definition popH: unit -> itree Es unit :=
    fun varg =>
    Ret tt
  .

  Definition pushH: unit -> itree Es unit :=
    fun varg =>
    Ret tt
  .

  Definition HSem: ModSem.t := {|
    ModSem.fnsems := [("popH", cfunU popH); ("pushH", cfunU pushH)];
    ModSem.init_st := (@nil val)↑; (* queue or list *)
  |}
  .
  Definition H: Mod.t := {|
    Mod.get_modsem := fun _ => HSem;
    Mod.sk := [("popH", Gfun↑ ); ("pushH", Gfun↑)];
  |}
  .

End H.


Section CC.
  (* Queue *)

  Definition pop: list val -> itree Es val := 
    fun varg =>
    st <- trigger sGet;;
    `l : (list val) <- st↓?;;
    let '(x, l) := match l with | h::t => (h, t) | _ => ((Vint 0), (@nil val)) end in
    trigger (sPut l↑);;; 
    Ret x
  .
  Definition push: list val -> itree Es val := 
    fun varg =>
    `x: val <- (pargs [Tuntyped] varg)?;;
    st <- trigger sGet;;
    `l : (list val) <- st↓?;;
    let l := l ++ [x] in
    trigger (sPut l↑);;;
    Ret Vundef
  .

  (* Debug *)
  (* Definition print: unit -> itree Es unit :=
    fun varg =>
      st <- trigger sGet;;
      `l : (list val) <- st↓?;;
      _ <- (ITree.iter
        (fun i =>
          _ <- (match i with
          | h::t => (printV h)
          | _ => (printV (Vint 0)) 
          end);;
          match i with
          | h::t => Ret (inl t)
          | _ => Ret (inr tt)
          end
        ) l);;

      Ret tt
    . *)



  Definition CCSem: ModSem.t := {|
    ModSem.fnsems := [("pop", cfunU pop); ("push", cfunU push)];
    (* ModSem.fnsems := [("pop", cfunU pop); ("push", cfunU push); ("print", cfunU print)]; *)
    ModSem.init_st := (@nil val)↑; (* queue or list *)
  |}
  .
  Definition CC: Mod.t := {|
    Mod.get_modsem := fun _ => CCSem;
    Mod.sk := [("pop", Gfun↑); ("push", Gfun↑); ("print", Gfun↑)];
  |}
  .

End CC.

Section F.
  (* Simple function using push, pop + @ *)
  (* getint x ; yield ; push 2*x ; yield *)
  Definition f: list val -> itree Es val :=
  fun varg =>
    `x: val <- (pargs [Tuntyped] varg)?;;
    (* _ <- trigger EventsL.Yield;; *)
    x <- (vadd x (Vint 1))?;;
    trigger (Call "push" [x]↑);;;
    (* _ <- trigger EventsL.Yield;; *)
    Ret Vundef
  .

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfunU f)];
    ModSem.init_st := tt↑;
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Gfun↑)];
  |}
  .

End F.

Section G.
  (* Simple function using push, pop + @*)
  (* yield; x = pop; yield; return x/2 *)
  Definition g: list val -> itree Es val :=
  fun varg =>
    (* _ <- trigger EventsL.Yield;; *)
    `x : val <- ccallU "pop" (@nil val);;
    (* _ <- trigger EventsL.Yield;; *)
    x <- (vsub x (Vint 1))?;;
    Ret x
  .


  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", cfunU g)];
    ModSem.init_st := tt↑;
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Gfun↑)];
  |}
  .

End G.

Section MAIN.
  Definition main : option mname * Any.t-> itree Es Any.t :=
  fun '(_, varg) =>
  trigger (EventsL.Spawn "threadF" (@nil val)↑);;; 
  trigger (EventsL.Spawn "threadF" (@nil val)↑);;; 
  trigger (EventsL.Spawn "threadF" (@nil val)↑);;; 
  trigger (EventsL.Spawn "threadG" (@nil val)↑);;; 
  trigger (EventsL.Spawn "threadG" (@nil val)↑);;; 
  trigger (EventsL.Spawn "threadG" (@nil val)↑);;; 
  trigger (EventsL.Spawn "threadP" (@nil val)↑);;; 

  Ret Vundef↑
  .
  
  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", main)];
    ModSem.mn := "Main";
    ModSem.initial_st := tt↑;
  |}
  .
  
  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .

End MAIN.


Section TH1.
  Definition threadF : option mname * Any.t-> itree Es Any.t :=
  fun '(_, varg) =>
    let i := (Vint 0) in
    `_:unit <- (ITree.iter
    ( fun i =>
    `_:val <- ccallU "f" [i];;
    i' <- (vadd i (Vint 1))?;;
    Ret (inl i')
    ) i );;

   
   Ret Vundef↑
  .

  Definition TH1Sem: ModSem.t := {|
    ModSem.fnsems := [("threadF", threadF)];
    ModSem.mn := "TH1";
    ModSem.initial_st := tt↑;

  |}
  .

  Definition TH1: Mod.t := {|
    Mod.get_modsem := fun _ => TH1Sem;
    Mod.sk := Sk.unit;
  |}
  .

End TH1.

Section TH2.
  Definition threadG : option mname * Any.t-> itree Es Any.t :=
    fun '(_, varg) =>
      `_:unit <- (ITree.iter
        ( fun _ =>
        `_:val <- ccallU "g" (@nil val);;
        Ret (inl tt)
        ) tt );;

   
   Ret Vundef↑
  .

  Definition TH2Sem: ModSem.t := {|
    ModSem.fnsems := [("threadG", threadG)];
    ModSem.mn := "TH2";
    ModSem.initial_st := tt↑;

  |}
  .

  Definition TH2: Mod.t := {|
    Mod.get_modsem := fun _ => TH2Sem;
    Mod.sk := Sk.unit;
  |}
  .


End TH2.

Section TH3. 
(* Print *)

  Definition threadP : option mname * Any.t -> itree Es Any.t :=
  fun '(_, varg) =>
  `_:unit <- (ITree.iter
        ( fun _ =>
        `_:val <- ccallU "print" tt;;
        _ <- trigger EventsL.Yield;;
        Ret (inl tt)
        ) tt
  );;

  Ret Vundef↑
.
  Definition TH3Sem: ModSem.t := {|
    ModSem.fnsems := [("threadP", threadP)];
    ModSem.mn := "TH3";
    ModSem.initial_st := tt↑;

  |}
  .

  Definition TH3: Mod.t := {|
    Mod.get_modsem := fun _ => TH3Sem;
    Mod.sk := Sk.unit;
  |}
  .

End TH3.