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


Definition update (env : Env ) ( x : string ) ( v : Result) : Env :=
  fun y =>
   if( eqb y x)
       then 
          if ( andb (check_eq_over_types err_undecl (env y)) (negb (check_eq_over_types default v)))
          then err_undecl 
          else
             if( andb (check_eq_over_types err_undecl (env y))  (check_eq_over_types default v))
             then default
             else
                 if (orb (check_eq_over_types default (env y)) (check_eq_over_types v (env y)))
                 then v 
                 else err_assign
   else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).



Compute (env "y").
Compute (update (update env "y" (default)) "y" (res_bool true) "y").
Compute (update env "a" (res_nat 100)) "a".
Compute (update (update env "y" (default)) "y" (res_string "true") "y").

Inductive AExp :=
  | avar: string -> AExp 
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | amin: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp 
  | adiv: AExp -> AExp -> AExp 
  | amod: AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (amin A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

Fixpoint aeval_fun (a : AExp) (env : Env) : ErrorNat :=
  match a with
  | avar v => match (env v) with
                | res_nat n => n
                | _ => error_nat
                end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amin a1 a2 => (sub_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  end.

Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.

Compute aeval_fun ("x" +' 3) (update (update env "x" (default)) "x" (res_nat 100) ).



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

Notation "A <' B" := (blt A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Definition gt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v2 v1)
    end.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Fixpoint beval_fun (a : BExp) (envnat : Env) : ErrorBool :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => error_bool
  | bvar v => match (env v) with
                | res_bool n => n
                | _ => error_bool
                end
  | blt a1 a2 => (lt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bgt a1 a2 => (gt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bnot b1 => (not_ErrorBool (beval_fun b1 envnat))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  end.

Inductive Stmt :=
  | nat_decl: string -> Stmt 
  | bool_decl: string  -> Stmt 
  | string_decl : string ->Stmt
  | vect_decl : string -> nat ->Stmt
  | struct_decl : string ->Stmt -> Stmt
  | nat_assign : string -> AExp -> Stmt 
  | bool_assign : string -> BExp -> Stmt 
  | string_assign : string -> string ->Stmt
  | var_assign : string -> string ->Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | for_each : string -> string -> nat -> Stmt-> Stmt.

Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "X :v= A" := (var_assign X A) (at level 90).
Notation "'iNat' X " := (nat_decl X)(at level 90).
Notation "'iBool' X " := (bool_decl X)(at level 90).
Notation "'iStr' X " := (string_decl X) (at level 90).
Notation "'Vect' X [' n ] " := (vect_decl X n) (at level 90).
Notation "'Struct' X {' S }" := (struct_decl X S) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'Cat_timp' (' B ) {' S }" := (while B S) (at level 93).
Notation "'Daca' (' B ) 'atunci' {' S } 'altfel' {' S2 }" := (ifthenelse B S S2) (at level 93).
Notation "'Daca' (' B ) 'atunci' {' S }" := (ifthen B S)( at level 93).
Notation "'Pentru_fiecare'  (' V , it , n )  {' S }" := (for_each V it n S) (at level 94).

Definition to_char (n: nat) : string :=
 match n with
  | 0 =>"0"
  | 1 =>"1"
  | 2 =>"2"
  | 3 =>"3"
  | 4 =>"4"
  | 5 =>"5"
  | 6 =>"6"
  | 7 =>"7"
  | 8 =>"8"
  | 9 =>"9"
  | _ =>"0"

 end.
 
Fixpoint decl_vect (env : Env) (s : string) (n: nat) : Env :=
 match n with
  | 0 => env
  | S n'=> decl_vect (update env (Concat (Concat (Concat s "[") (to_char n') ) "]") default) s n'
 end.

Definition vect (env : Env) (s : string) (r: Result) : Env :=
  update env s r.

Definition decl_check (s: Stmt) : nat :=
match s with
 | nat_decl a => 1
 | bool_decl a=> 2
 | string_decl a => 3
 | _ => 0
end.

Definition struct_concat (s1 s2 :string) : string :=
 Concat (Concat s1 ".") s2.
Definition vect_concat (s1 :string) (n:nat) : string :=
 Concat (Concat (Concat s1 "[") (to_char n)) "]".
Compute struct_concat "a" "m".
Compute vect_concat "x" 5.

Compute (update env (struct_concat "s" "x") default) "s.x".
Compute (update (update env (struct_concat "s" "x") default) (struct_concat "s" "x") (res_nat 0)) "s.x" .

Fixpoint decl_struct ( env : Env) (s: string) (a : Stmt) : Env :=
match a with
 | sequence b c =>if(Nat.ltb 0 (decl_check b))
                  then match b with
                       | nat_decl x => decl_struct (update (update env (struct_concat s x) default) (struct_concat s x) (res_nat 0) ) s c
                       | bool_decl x => decl_struct (update (update env (struct_concat s x) default) (struct_concat s x) (res_bool true) ) s c
                       | string_decl x => decl_struct (update (update env (struct_concat s x) default) (struct_concat s x) (res_string "") ) s c
                       | _ => env
                       end
                  else env
 |nat_decl x => update (update env (struct_concat s x) default) (struct_concat s x) (res_nat 0)
 | bool_decl x => update (update env (struct_concat s x) default) (struct_concat s x) (res_bool true) 
 | string_decl x => update (update env (struct_concat s x) default) (struct_concat s x) (res_string "")
 | _ => env
end.

Compute (decl_struct env "x" ( iNat "a" ;; iNat "b")) "x.b".
Compute (decl_struct env "x" ( iNat "a" ;; iBool "b";; iStr "c")) "x.c".

Compute (decl_vect env "x" 4 ) "x[0]".
Compute (vect (decl_vect env "x" 4 ) "x[3]" (res_nat 6))"x[3]".




Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas'
                | nat_decl a => update (update env a default) a (res_nat 0)
                | bool_decl b => update (update env b default) b (res_bool true)
                | string_decl s => update env s default 
                | vect_decl s n => decl_vect env s n
                | struct_decl s n => decl_struct env s n
                | nat_assign a aexp => update env a (res_nat (aeval_fun aexp env))
                | bool_assign b bexp => update env b (res_bool (beval_fun bexp env))
                | string_assign s str => update env s (res_string str)
                | var_assign s1 s2 =>if(check_eq_over_types (env s1) (env s2))
                                     then update env s1 (env s2)
                                     else env
                | ifthen cond s' => 
                    match (beval_fun cond env) with
                    | error_bool => env
                    | boolean v => match v with
                                 | true => eval_fun s' env gas'
                                 | false => env
                                 end
                    end
                | ifthenelse cond S1 S2 => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v  => match v with
                                 | true => eval_fun S1 env gas'
                                 | false => eval_fun S2 env gas'
                                 end
                         end
                | while cond s' => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v => match v with
                                     | true => eval_fun (s' ;; (while cond s')) env gas'
                                     | false => env
                                     end
                        end
                | for_each V it n St=>
                                  match n with
                                      | 0 => eval_fun St (update env it (env (vect_concat V 0))) gas'
                                      | S n' => eval_fun (St ;; for_each V it n' St) (update env it (env (vect_concat V n))) gas'
                                  end
                end
    end.

Compute ((eval_fun ( iBool "b" ;; "b" :b=btrue)) env 100 "b") .

Compute ((eval_fun ( iStr "a" ;; "a" :s=(strcat("test","abc"))) env 100) "a") .
Compute (eval_fun ( Vect "x" [' 5 ];; "x[3]" :n= 10 ) env 100) "x[3]".
Compute (eval_fun ( Struct "X" {' iNat "a" ;; iBool "b";; iStr "c" } ;; "X.a" :n= 10 ) env 100) "X.a".

Definition Test1:=
 iNat "a";;
 "a" :n=5 ;;
 Daca ('"a" <' 7 ) atunci {' "a" :n= 10 }.

Compute (eval_fun Test1 env 100) "a".

Definition xD :=
 iNat "a" ;; iNat "b" ;; iNat "c";;
 "a" :n= 5 ;; "b" :n= 2 ;; "c" :n= "c" +' "b".

Compute (eval_fun xD env 100) "c".

Definition Test :=
Vect "x" [' 5 ] ;;
 "x[2]" :n=2;;
 "x[3]" :n=10 ;;
 "x[1]" :n=5 ;;
 "x[0]" :n=1 ;;
 iNat "it" ;;
 iNat "sum" ;;
 "sum" :n=0 ;;
 Pentru_fiecare ('"x" , "it" , 3 )  {' "sum" :n= "sum" +' "it" }.


Compute (eval_fun Test env 100) "sum".
