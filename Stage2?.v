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


Compute Concat "abc"  "bcd".

Fixpoint Strl (s1 : string) : nat :=
 match s1 with
 | EmptyString =>0
 | String c s1' => S (Strl s1')
end.


Compute Strl "a2414xd" .

Compute eqb "ab"  "abc" .

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
  | res_string : string -> Result
  | err_str : Result.
  
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
   |err_str => match t2 with
                | err_str => true
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
  | amod: AExp -> AExp -> AExp
  | alength: string -> AExp.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (amin A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "'STRLen' (' A )" := (alength A) (at level 50).

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

Definition length_ErrorNat (r:Result) : ErrorNat :=
match r with
 | res_string s => Strl s
 | _ =>0
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
  | alength S1 => length_ErrorNat (env S1)
  end.

Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.

Compute aeval_fun ("x" +' 3) (update (update env "x" (default)) "x" (res_nat 100) ).
Compute aeval_fun (STRLen ('"x" )) (update (update env "x" (default)) "x" (res_string "test") ).
Compute aeval_fun ( STRLen ('"abcd" ) +' 5 ) env.


Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=> match (sigma v) with
                                               | res_nat v =>v
                                               | _ =>error_nat
                                             end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_ErrorNat i1  i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_ErrorNat i1  i2) ->
    a1 *' a2 =[sigma]=> n
| diff : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_ErrorNat i1  i2) ->
    a1 -' a2 =[sigma]=> n
| div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_ErrorNat i1  i2) ->
    a1 /' a2 =[sigma]=> n
| modlo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_ErrorNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Require Import Omega.
Example ex1 : 5 %' 3 =[ env ]=> 2.
Proof.
eapply modlo.
 -apply const.
 -apply const.
 -simpl.
 reflexivity.
Qed.
Example ex2 : 7 /' 3 =[ env ]=> 2.
Proof.
  eapply div.
  - apply const.
  - apply const.
  -simpl.
   reflexivity.
Qed.
Example ex3 : 5 -' 7 =[ env ]=> error_nat.
Proof.
 eapply diff.
 -apply const.
 -apply const.
 -simpl.
 reflexivity.
Qed.
Example ex4 : "n" +' 2 =[ env ]=> error_nat.
Proof.
 eapply add.
 -apply var.
 -apply const.
 -simpl.
 reflexivity.
Qed.


Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bgt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp
  | bstr : string -> string -> BExp.

Notation "A <' B" := (blt A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).
Notation "'STRCmp' (' A , B )" := (bstr A B) (at level 50).

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

Definition res_ErrorBool (r1 r2 : Result) : ErrorBool :=
match r1,r2 with
| res_string s1, res_string s2 => eqb s1 s2
| _,_ => false
end.
 
Compute res_ErrorBool (res_string "test") (res_string "tet").
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
  | bstr s1 s2=> res_ErrorBool (envnat s1) (envnat s2)
  end.

Compute beval_fun (STRCmp ('"A", "B" )) (update (update (update (update env "A" (default)) "A" (res_string "tet")) "B" (default)) "B" (res_string "test")).

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=>  true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | res_bool x => x
                                                | _ => error_bool
                                                end
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_ErrorBool i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| e_greatthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (gt_ErrorBool i1 i2) ->
    a1 >' a2 ={ sigma }=> b
| e_not : forall b1 i1 sigma b,
    b1 ={ sigma }=> i1 ->
    b = ( not_ErrorBool i1 ) ->
    (bnot b1) ={ sigma }=> b
| e_and : forall b1 b2 i1 i2 sigma b,
    b1 ={ sigma }=> i1 ->
    b2 ={ sigma }=> i2 ->
    b = ( and_ErrorBool i1 i2 ) ->
    (band b1 b2) ={ sigma }=> b
| e_or : forall b1 b2 i1 i2 sigma b,
    b1 ={ sigma }=> i1 ->
    b2 ={ sigma }=> i2 ->
    b = ( or_ErrorBool i1 i2 ) ->
    (bor b1 b2) ={ sigma }=> b
where "B ={ S }=> B'" := (beval B S B').

Example bex1 : 5 <' 9 ={ env }=> true.
Proof.
  eapply e_lessthan.
  - eapply const.
  - eapply const.
  - simpl. reflexivity.
Qed.

Example bex2 : "n" <' 10 ={ env }=> error_bool.
Proof.
 eapply e_lessthan.
 -apply var.
 -apply const.
 -simpl. reflexivity.
Qed.

Example bex3 : !' (5 >'7) ={ env }=> true.
Proof.
 eapply e_not.
 -eapply e_greatthan.
  apply const.
  apply const.
 simpl.
 reflexivity.
 -simpl.
 reflexivity.
Qed.

Inductive Stmt :=
  | nat_decl: string -> Stmt 
  | bool_decl: string  -> Stmt 
  | string_decl : string ->Stmt
  | vect_decl : string -> nat ->nat->Stmt
  | struct_decl : string ->Stmt -> Stmt
  | nat_assign : string -> AExp -> Stmt 
  | bool_assign : string -> BExp -> Stmt 
  | string_assign : string -> string ->Stmt
  | var_assign : string -> string ->Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | for_each : string -> string -> nat -> Stmt-> Stmt
  | Caz : ErrorNat ->Stmt -> Stmt
  | switch_case : AExp -> Stmt -> Stmt
  | Copy_str : string -> string -> Stmt
  | Concat_str : string -> string -> Stmt.


Notation "'Case' (' A ) {' S }" := (Caz A S) (at level 95).
Notation "'Switch' (' A ) : {' S } " := (switch_case A S) ( at level 93).
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "X :v= A" := (var_assign X A) (at level 90).
Notation "'iNat' X " := (nat_decl X)(at level 90).
Notation "'iBool' X " := (bool_decl X)(at level 90).
Notation "'iStr' X " := (string_decl X) (at level 90).
Notation "'nVect' X [' n ] " := (vect_decl X n 1) (at level 90).
Notation "'bVect' X [' n ] " := (vect_decl X n 2) (at level 90).
Notation "'sVect' X [' n ] " := (vect_decl X n 3) (at level 90).
Notation "'Struct' X {' S }" := (struct_decl X S) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'Cat_timp' (' B ) {' S }" := (while B S) (at level 93).
Notation "'Daca' (' B ) 'atunci' {' S } 'altfel' {' S2 }" := (ifthenelse B S S2) (at level 93).
Notation "'Daca' (' B ) 'atunci' {' S }" := (ifthen B S)( at level 93).
Notation "'Pentru_fiecare'  (' V , it , n )  {' S }" := (for_each V it n S) (at level 94).
Notation "'Strcpy' (' S1 , S2 )":= (Copy_str S1 S2) (at level 93).
Notation "'Strcat' (' S1 , S2 )":= (Concat_str S1 S2) (at level 93).

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
 
Definition vect_concat (s1 :string) (n:nat) : string :=
 Concat (Concat (Concat s1 "[") (to_char n)) "]".

Definition res_check (n: nat) : Result :=
match n with
 | 1 => res_nat 0 
 | 2 => res_bool true
 | 3 => res_string "" 
 | _ => default
end.

Definition decl_check (s: Stmt) : nat :=
match s with
 | nat_decl a => 1
 | bool_decl a=> 2
 | string_decl a => 3
 | _ => 0
end.

Fixpoint decl_vect (env : Env) (s : string) (n tip: nat) : Env :=
 match n with
  | 0 => env
  | S n'=> decl_vect (update (update env (vect_concat s n') default) (vect_concat s n') (res_check tip) ) s n' tip
 end.

Definition vect (env : Env) (s : string) (r: Result) : Env :=
  update env s r.



Definition struct_concat (s1 s2 :string) : string :=
 Concat (Concat s1 ".") s2.

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

Definition Concat_res (r1 r2 :Result) :Result :=
match r1,r2 with
| res_string s1, res_string s2 => res_string (Concat s1 s2)
| _,_ => err_str
end.

Compute (decl_struct env "x" ( iNat "a" ;; iNat "b")) "x.b".
Compute (decl_struct env "x" ( iNat "a" ;; iBool "b";; iStr "c")) "x.c".

Compute (decl_vect env "x" 4 3 ) "x[0]".
Compute (vect (decl_vect env "x" 4 1) "x[3]" (res_nat 6))"x[3]".



Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas'
                | nat_decl a => update (update env a default) a (res_nat 0)
                | bool_decl b => update (update env b default) b (res_bool true)
                | string_decl s => update env s default 
                | vect_decl s n m=> decl_vect env s n m
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
                | Caz n St =>eval_fun St env gas'
               
                | switch_case AE C =>
                                 match C with
                                         | Caz n St => if(ErrorNat_beq n (aeval_fun AE env))  
                                                       then eval_fun St env gas'
                                                        else env
                                          | sequence S1 S2 => match S1 with    
                                                              | Caz n St => if(ErrorNat_beq n (aeval_fun AE env))  
                                                                            then eval_fun St env gas'   
                                                                            else eval_fun (switch_case AE S2) env gas'
                                                               | _ => env
                                                                end
                                         | _ => env
                                 end
                | for_each V it n St=>
                                  match n with
                                      | 0 => eval_fun St (update env it (env (vect_concat V 0))) gas'
                                      | S n' => eval_fun (St ;; for_each V it n' St) (update env it (env (vect_concat V n))) gas'
                                      end
                 | Copy_str S1 S2 => update env S1 (env S2) 
                 | Concat_str S1 S2 => update env S1 (Concat_res (env S1) (env S2))               
                end
    end.


Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Check update.
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_assigN: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (res_nat i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_assigB: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_assigS: forall a x sigma sigma',
    sigma' = (update sigma x (res_string a)) ->
    (x :s= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_iffalse : forall b s s' sigma sigma',
  b ={ sigma }=> false ->
  s' -{ sigma }->sigma' ->
  ifthenelse b s s' -{ sigma }->sigma'
| e_iftrue : forall b s s' sigma sigma',
  b ={ sigma }=> true ->
  s -{ sigma }->sigma' ->
  ifthenelse b s s' -{ sigma }->sigma' 
  
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Compute ((eval_fun ( iBool "b" ;; "b" :b=btrue)) env 100 "b") .
Compute (eval_fun ( iStr "c" ;; "c" :s="test" ;; iNat "nr" ;; "nr" :n= (STRLen ('"c" ) )) env 100) "nr".

Compute ((eval_fun ( iStr "a" ;; "a" :s=(Concat "test" "abc")) env 100) "a") .
Compute (eval_fun ( nVect "x" [' 5 ];; "x[3]" :n= 10 ) env 100) "x[4]".
Compute (eval_fun ( Struct "X" {' iNat "a" ;; iBool "b";; iStr "c" } ;; "X.a" :n= 10 ) env 100) "X.c".

Compute (eval_fun ( iStr "A" ;; iStr "B" ;; "B" :s= "rest" ;; Strcpy (' "A" , "B" ) ) env 100) "A".
Compute (eval_fun ( iStr "A" ;; iStr "B" ;; "B" :s= "rest" ;; Strcpy (' "A" , "B" );; Strcat (' "A" , "B" ) ) env 100) "A".


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
nVect "x" [' 5 ] ;;
 "x[2]" :n=2;;
 "x[3]" :n=10 ;;
 "x[1]" :n=5 ;;
 "x[0]" :n=1 ;;
 iNat "it" ;;
 iNat "sum" ;;
 "sum" :n=0 ;;
 Pentru_fiecare ('"x" , "it" , 2 )  {' "sum" :n= "sum" +' "it" }.


Compute (eval_fun Test env 100) "sum".

Definition Checkq :=
iNat "a" ;;
iNat "b" ;;
"a" :n= 3 +' 4 ;;
Switch ('"a" ) : {'
Case ('2) {' "b" :n= 2};;
Case ('7) {' "b" :n= 7};;
Case ('15) {' "b" :n= 15}
}.

Compute (eval_fun Checkq env 100) "b". 






