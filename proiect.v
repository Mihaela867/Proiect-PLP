(*Variables and environment*)
Require Import String.

Inductive ValueTypes:=
| natural : nat -> ValueTypes
| boolean : bool -> ValueTypes
| String : string -> ValueTypes.

Scheme Equality for ValueTypes.

Definition Env := string -> ValueTypes.

(* Arithmetic expressions *)

 Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

 
Coercion avar : string >-> AExp.
Coercion anum : nat >-> AExp.
Notation "A +' B" := (aplus A B) (at level 48, right associativity).
Notation "A -' B" := (amin A B) (at level 48, right associativity).
Notation "A *' B" := (amul A B) (at level 38, left associativity).
Notation "A \' B" := (adiv A B) (at level 38, left associativity).
Notation "A %' B" := (amod A B) (at level 37, left associativity).

(* Boolean expressions *)

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.

Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bgreaterthan A B) (at level 70).
Notation "! A" := (bnot A)(at level 50).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 80).

(*Statements*)

Inductive Stmt :=
| assignment : string -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt->Stmt.

Inductive List:=
| nil
| cons (n:ValueTypes)(l: List)
| cons' (exp : Stmt) (l:List).

Inductive switch :=
| switchCase: AExp -> List -> List -> switch.


Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).


Check ifthen (3<'2) ("a" ::= 3).
Check 1+'2.
Check switchCase (3+'2) (cons (natural 6) (nil)) (cons' ("a" ::= 4)(nil)).
Check switchCase (3+'2) (cons (natural 6) ((cons (natural 7) (nil))))  (cons' ("a" ::= 4)((cons' ("b" ::= 4)(nil)))). 

(* String operations*)

Inductive StringOp :=
| concat: string -> string -> StringOp
| compare: string -> string -> StringOp
| length: string -> StringOp
| Sassignment: string -> string -> StringOp.

(*Arrays*)

Definition Array:= nat -> ValueTypes.

Definition array0 : Array :=
  fun x =>
    if (Nat.eqb x 0)
    then natural 10
    else natural 0.

Compute array0 0.
Compute array0 1.