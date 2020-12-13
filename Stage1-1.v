Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.

(* op cu string*)
Compute eqb "ab" "ac".

Fixpoint Concat (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (Concat s1' s2)
  end.

Notation "strcat( x , y )" := (Concat x y) (at level 60).
Compute strcat( "abc" , "bcd").

Fixpoint Strl (s1 : string) : nat :=
 match s1 with
 | EmptyString =>0
 | String c s1' => S (Strl s1')
end.

Notation "strlen( x )" := (Strl x) (at level 62).
Compute strlen( "a2414xd" ).

Notation "strcmp( x , y )" := (eqb x y) (at level 64).

Compute strcmp( "ab" , "abc" ).

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive AExp :=
  | avar: string -> AExp 
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | amin: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp 
  | adiv: AExp -> AExp -> AExp 
  | amod: AExp -> AExp -> AExp.

Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.


...
