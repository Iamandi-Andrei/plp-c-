Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.

Inductive ValueTypes :=
| Int : string -> ValueTypes
| Bool : string -> ValueTypes
| Nat : nat -> ValueTypes
| mbool : nat -> ValueTypes.
Definition value (n:ValueTypes) : nat :=
match n with
| Nat n =>n
| mbool n => if(Nat.leb 0 n)
             then 1
             else 0
| _ => 0
end.

Scheme Equality for ValueTypes.
Definition Env := string -> ValueTypes.

Definition global : Env :=
  fun x =>
    if (ValueTypes_eq_dec (Int x) (Int "a"))
    then Nat 10
    else  Nat 0.
Check global.
Compute (global  "a").
