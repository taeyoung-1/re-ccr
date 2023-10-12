Require Import ConvC2ITree.
Require Import Clight_Mem0.
Require Import Clight_Mem1.
Require Import BinNums.
From compcertip Require Import Clightdefs Integers.
Module CTypeNotation.
Declare Scope ctypes_scope.
Bind Scope ctypes_scope with Ctypes.type.
Notation "'_v#'" := tvoid (at level 100)  : ctypes_scope.
Notation "'_sc#'" := tschar (at level 100) : ctypes_scope.
Notation "'_uc#'" := tuchar (at level 100) : ctypes_scope.
Notation "'_s#'" := tshort (at level 100) : ctypes_scope.
Notation "'_us#'" := tushort (at level 100) : ctypes_scope.
Notation "'_i#'" := tint (at level 100) : ctypes_scope.
Notation "'_ui#'" := tuint (at level 100) : ctypes_scope.
Notation "'_b#'" := tbool (at level 100) : ctypes_scope.
Notation "'_l#'" := tlong (at level 100) : ctypes_scope.
Notation "'_ul#'" := tulong (at level 100) : ctypes_scope.
Notation "'_f#'" := tfloat (at level 100) : ctypes_scope.
Notation "'_d#'" := tdouble (at level 100) : ctypes_scope.
Notation "'_pv#'" := (tptr tvoid) (at level 100) : ctypes_scope.
Notation "'_psc#'" := (tptr tschar) (at level 100) : ctypes_scope.
Notation "'_puc#'" := (tptr tuchar) (at level 100) : ctypes_scope.
Notation "'_ps#'" := (tptr tshort) (at level 100) : ctypes_scope.
Notation "'_pi#'" := (tptr tint) (at level 100) : ctypes_scope.
Notation "'_pui#'" := (tptr tuint) (at level 100) : ctypes_scope.
Notation "'_pb#'" := (tptr tbool) (at level 100) : ctypes_scope.
Notation "'_pl#'" := (tptr tlong) (at level 100) : ctypes_scope.
Notation "'_pul#'" := (tptr tulong) (at level 100) : ctypes_scope.
Notation "'_pf#'" := (tptr tfloat) (at level 100) : ctypes_scope.
Notation "'_pd#'" := (tptr tdouble) (at level 100) : ctypes_scope.
Notation "tp [ sz ]" := (tarray tp sz) (at level 100, sz at level 7) : ctypes_scope.
Notation "_[ x ; .. ; y ]" := ((Ctypes.Tcons x ( .. (Ctypes.Tcons y Ctypes.Tnil) .. )))
                                (at level 100, x, y at level 8) : ctypes_scope.
Notation "_( x 't->' y )" := (Ctypes.Tfunction x y AST.cc_default) (at level 100, x, y at level 8) : ctypes_scope.
End CTypeNotation.

Module CExpNotation.
Declare Scope cexp_scope.
Bind Scope cexp_scope with Clight.expr.
Notation " e1 #+ e2 "
  := (Clight.Ebinop Cop.Oadd e1 e2 _)
       (at level 50, e2 at level 59) : cexp_scope.
(* Check (Clight.Ebinop Cop.Oadd (Clight.Evar xH Tvoid) (Clight.Evar xH Tvoid) Tvoid). *)
(* Check {Clight.Evar xH Tvoid +# Clight.Evar xH Tvoid}_Tvoid. *)
Notation "{ e1 #- e2 }  tp"
  := (Clight.Ebinop Cop.Osub e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #* e2 }  tp"
  := (Clight.Ebinop Cop.Omul e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #/ e2 }  tp"
  := (Clight.Ebinop Cop.Odiv e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #% e2 }  tp"
  := (Clight.Ebinop Cop.Omod e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #& e2 }  tp"
  := (Clight.Ebinop Cop.Oand e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #| e2 }  tp"
  := (Clight.Ebinop Cop.Oor e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #^ e2 }  tp"
  := (Clight.Ebinop Cop.Oxor e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #<< e2 }  tp"
  := (Clight.Ebinop Cop.Oshl e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #>> e2 }  tp"
  := (Clight.Ebinop Cop.Oshr e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #== e2 }  tp"
  := (Clight.Ebinop Cop.Oeq e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
Notation "{ e1 #=! e2 }  tp"
  := (Clight.Ebinop Cop.One e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
 Notation "{ e1 #< e2 }  tp"
  := (Clight.Ebinop Cop.Olt e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
 Notation "{ e1 #> e2 }  tp"
  := (Clight.Ebinop Cop.Ogt e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
 Notation "{ e1 #<= e2 }  tp"
  := (Clight.Ebinop Cop.Ole e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.
 Notation "{ e1 #>= e2 }  tp"
  := (Clight.Ebinop Cop.Oge e1 e2 tp)
       (at level 50, e1 at level 9, e2 at level 9, tp at level 8) : cexp_scope.

 (* notbool notint neg absfloat *)
 Notation "{ ! e }  tp"
   := (Clight.Eunop Cop.Onotbool e tp) (at level 50, e at level 9, tp at level 8) : cexp_scope.
 Notation "{ ~ e }  tp"
   := (Clight.Eunop Cop.Onotint e tp) (at level 50, e at level 9, tp at level 8) : cexp_scope.
 Notation "{ - e }  tp"
   := (Clight.Eunop Cop.Oneg e tp) (at level 50, e at level 9, tp at level 8) : cexp_scope.
 Notation "{ 'abs' e }  tp"
   := (Clight.Eunop Cop.Oabsfloat e tp) (at level 50, e at level 9, tp at level 8) : cexp_scope.

  Notation "[ e ]↑ tp"
    := (Clight.Ecast e tp) (at level 50, e at level 9, tp at level 8) : cexp_scope.
  Notation "[ bin ]v tp"
    := (Clight.Evar bin tp) (at level 50, bin at level 9, tp at level 8) : cexp_scope.
  Notation "[ bin ]t tp"
    := (Clight.Etempvar bin tp) (at level 50, bin at level 9, tp at level 8) : cexp_scope.
  Notation "#i i"
    := (Clight.Econst_int (Int.repr i) tint) (at level 50) : cexp_scope.
  Notation "[ f ]f tp"
    := (Clight.Econst_float f tp) (at level 50, f at level 9, tp at level 8) : cexp_scope.
  Notation "[ s ]s tp"
    := (Clight.Econst_single s tp) (at level 50, s at level 9, tp at level 8) : cexp_scope.
  Notation "[ l ]l tp"
    := (Clight.Econst_long l tp) (at level 50, l at level 9, tp at level 8) : cexp_scope.

  Notation "#! e tp"
    := (Clight.Ederef e tp) (at level 50, e at level 9, tp at level 8) : cexp_scope.
  Notation "#& e tp"
    := (Clight.Eaddrof e tp) (at level 50, e at level 9, tp at level 8) : cexp_scope.
  Notation " e #$ bin tp"
    := (Clight.Efield e bin tp) (at level 50, tp at level 8) : cexp_scope.

  Notation "'#sizeof' t tp"
    := (Clight.Esizeof t tp) (at level 50, t, tp at level 8) : cexp_scope.
  Notation "'#alignof' t tp"
    := (Clight.Ealignof t tp) (at level 50, t, tp at level 8) : cexp_scope.
End CExpNotation.

Module CStmtNotation.
Declare Scope cstmt_scope.
Bind Scope cstmt_scope with Clight.statement.

Notation "'skip'" := Clight.Sskip (at level 100) : cstmt_scope.
Notation "e1 '<<=' e2" := (Clight.Sassign e1 e2) (at level 60, e2 at level 50) : cstmt_scope.
Notation "x '#=' e" := (Clight.Sset x e) (at level 60) : cstmt_scope.
Notation "x '#=' f l" := (Clight.Scall (Some x) f l) (at level 60, f at level 9) : cstmt_scope.
Notation "'_' '#=' f l " := (Clight.Scall None f l) (at level 60, f at level 9) : cstmt_scope.
(* Notation "" := (Clight.Sbuiltin () ) *)
Notation "s1 '#;;;' s2" := (Clight.Ssequence s1 s2)
                        (at level 61, left associativity,
                          format "'[v' s1 '#;;;' '/' '/' '[' s2 ']' ']'") : cstmt_scope.
Notation "'if' e 'then' s1 'else' s2 'fi'" := (Clight.Sifthenelse e s1 s2)
                                           (at level 100, right associativity,
                                             format "'[v' 'if'  e '/' '[hv' 'then'  s1  '/' 'else'  s2 ']' '/' 'fi' ']'") : cstmt_scope.
Notation "'ret' e" := (Clight.Sreturn (Some e)) (at level 60, e at level 50) : cstmt_scope.
Notation "'ret' 'void'" := (Clight.Sreturn None) (at level 60) : cstmt_scope.
Notation "x '#:' s" := (Clight.Slabel x s) (at level 60) : cstmt_scope.
Notation "'jump' x" := (Clight.Sgoto x) (at level 60) : cstmt_scope.
Notation "'loop1' '{' x '}' 'loop2' '{' y '}'"
  := (Clight.Sloop x y)
       (at level 60, format  "'[v' 'loop1' '{' '/  ' x '/' '}' '/' 'loop2' '{' '/  ' y '/' '}' ']'") : cstmt_scope.
Notation "'while' '(' x ')' '{' y '}'"
  := (Clight.Swhile x y)
       (at level 60, format "'[v' 'while' '(' x ')' '{' '/  ' y '/' '}' ']' ") : cstmt_scope.
Notation "'do' '{' x '}' 'while' '(' y ')'"
  := (Clight.Sdowhile x y)
       (at level 60, format "'[v' 'do' '{' '/  ' x '/' '}' 'while' '(' y ')' ']'") : cstmt_scope.
Notation "'for' '(' i '#;;;' br '#;;;' u ')' '{' bd '}'"
  := (Clight.Sfor i br bd u)
       (at level 60,
         format "'[v' 'for' '(' i '#;;;' br '#;;;' u ')' '{' '/  ' bd '/' '}' ']'") : cstmt_scope.
Notation "'break'" := Clight.Sbreak (at level 100) : cstmt_scope.
Notation "'continue'" := Clight.Scontinue (at level 100) : cstmt_scope.
Notation "'#switch' e '#case' lsl"
  := (Clight.Sswitch e lsl) (at level 100, format "'[v' '#switch' e '#case' '/' lsl ']'") : cstmt_scope.
Definition consuc : (option BinNums.Z) * Clight.statement -> Clight.labeled_statements -> Clight.labeled_statements := fun '(x , s) => Clight.LScons x s.
End CStmtNotation.