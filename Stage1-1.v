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
Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | res_string : string -> Result.
  
Scheme Equality for Result.


Definition Env := string -> Result.

Definition env : Env := fun x => err_undecl.

Definition check_eq_over_types (t1 : Result) (t2 : Result) : bool :=
  match t1 with
    | err_undecl => match t2 with
                    |err_undecl => true
                    | _ => false
                    end
    | err_assign => match t2 with 
                     | err_assign => true
                     | _ => false
                     end
    |default => match t2 with
                     | default => true
                     | _ => false
                      end
    |res_nat n  => match t2 with
                     | res_nat a => true
                     | _ => false
                      end
    |res_bool n => match t2 with
                     | res_bool a => true
                     | _ => false
                      end
   |res_string a => match t2 with
                     | res_string b => true
                     | _ => false
                      end
  end.
Compute (check_eq_over_types (res_bool (boolean true)) (res_nat 100)).

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
  | bgt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.


...
