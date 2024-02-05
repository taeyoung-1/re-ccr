Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import Imp.




Section H.
  (* Queue *)

  Definition popH: list val -> itree Es val := 
    fun varg =>
    st <- trigger sGet;;
    `l : (list val) <- st↓?;;
    let '(x, l) := match l with | h::t => (h, t) | _ => ((Vint 0), (@nil val)) end in
    x <- (vsub x (Vint 1))?;;
    trigger (sPut l↑);;; 
    Ret x
  .
  Definition pushH: list val -> itree Es val := 
    fun varg =>
    `x: val <- (pargs [Tuntyped] varg)?;;
    st <- trigger sGet;;
    `l : (list val) <- st↓?;;
    x <- (vadd x (Vint 1))?;;
    let l := l ++ [x] in
    trigger (sPut l↑);;;
    Ret Vundef
  .
  Definition HSem: ModSem.t := {|
    ModSem.fnsems := [("popH", cfunU popH); ("pushH", cfunU pushH)];
    ModSem.init_st := (@nil val)↑; (* queue or list *)
  |}
  .
  Definition H: Mod.t := {|
    Mod.get_modsem := fun _ => HSem;
    Mod.sk := [("popH", Gfun↑); ("pushH", Gfun↑)];
  |}
  .

End H.

Section CC.
  Definition pop: unit -> itree Es unit :=
  fun varg =>
    Ret tt
  .

  Definition push: unit -> itree Es unit :=
  fun varg =>
    Ret tt
  .

  Definition CCSem: ModSem.t := {|
    ModSem.fnsems := [("pop", cfunU pop); ("push", cfunU push)];
    ModSem.mn := "CC";
    ModSem.initial_st := tt↑; (* queue or list *)
  |}
  .
  Definition CC: Mod.t := {|
    Mod.get_modsem := fun _ => CCSem;
    Mod.sk := [("pop", Gfun↑); ("push", Gfun↑)];
  |}
  .


End CC.

Section F.
  (* Simple function using push, pop + @ *)
  (* getint x ; yield ; push x ; yield *)
  Definition f: list val -> itree Es val :=
  fun varg =>
    `x: val <- (pargs [Tuntyped] varg)?;;
    _ <- trigger EventsL.Yield;;
    trigger (Call "pushH" [x]↑);;;
    _ <- trigger EventsL.Yield;;
    Ret Vundef
  .

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfunU f)];
    ModSem.mn := "F";
    ModSem.initial_st := tt↑;
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
  (* yield; x = pop; yield; return x *)
  Definition g: list val -> itree Es val :=
  fun varg =>
    _ <- trigger EventsL.Yield;;
    `x : val <- ccallU "popH" (@nil val);;
    _ <- trigger EventsL.Yield;;
    Ret x
  .


  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", cfunU g)];
    ModSem.mn := "G";
    ModSem.initial_st := tt↑;
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
  trigger (Call "pushH" [(Vint 10)]↑);;;
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