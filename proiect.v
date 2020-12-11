(*Variables and environment*)
Require Import String.

Inductive Value:=
| undeclared : Value
| defined : Value
| natural : nat -> Value
| boolean : bool -> Value
| String : string -> Value.

Scheme Equality for Value.

Definition Env := string -> Value.
Definition Memory := nat -> Value.
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
Require Import Coq.Lists.List.
Import ListNotations.

Inductive Stmt :=
| assignment : string -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt->Stmt.
(* 
Inductive List:=
| nil
| cons (n:Value)(l: List)
| cons' (exp : Stmt) (l:List). *)

Inductive cases :=
| case : AExp -> Stmt -> cases
| defaultCase : Stmt -> cases.

Inductive switch :=
| switchCase: AExp -> list cases -> switch.


Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).

Check ifthen (3<'2) ("a" ::= 3).
Check 1+'2.
Compute [ 1 ].
Check switchCase (1+'2) [defaultCase ("a" ::= 2)].
Check switchCase (avar "a")
    [case (5) ("a" ::= 4);
     defaultCase ("a" ::= 0)].

(* String operations*)

Inductive StringOp :=
| concat: string -> string -> StringOp
| compare: string -> string -> StringOp
| Slength: string -> StringOp
| Sassignment: string -> string -> StringOp.

Check concat "ana" "maria".


(*Arrays*)

(* ++declare arrays??? *)
Definition Array:= nat -> Value.

Definition array0 : Array :=
  fun x =>
    if (Nat.eqb x 0)
    then natural 10
    else natural 0.

Compute array0 0.
Compute array0 1.

Inductive ArrayOp :=
| Alength : Array -> ArrayOp
| push: Array -> Value -> ArrayOp
| delete: Array -> nat -> ArrayOp
| pop: Array -> ArrayOp.

Check Alength array0.


(* Struct *)

Inductive Members := 
| member : Type -> string -> Value -> Members.

Inductive struct := 
| Struct : (list Members) -> struct.

Compute Struct [member nat "a" defined].
Compute Struct [member bool "b" (boolean true); 
                member nat "x" (defined)].


(* Inductive Var :=
| defaultV
| naturalv : string ->nat->Var.

Inductive memberList:=
| nill
| member (t:Type) (v:Var).

(* Inductive struct:= 
|members: string -> memberList->struct.
 *)
Definition struct := string->memberList.
Definition struct1 (s:string) ()  : struct :=
    

Definition Env := Var -> nat.
Definition env1 : Env :=
  fun x =>
    if (Var_eq_dec x n)
    then 10
    else if (Var_eq_dec x x)
    then 15
    else 0. *)

(* pointeri si referinte*)
