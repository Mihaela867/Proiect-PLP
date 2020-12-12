(*Variables and environment*)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.


Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString := 
| error_string : ErrorString
| String : string -> ErrorString.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion String : string >-> ErrorString.

Inductive Value:=
| undeclared : Value
| default : Value
| err_assign : Value
| nat_value : ErrorNat -> Value
| bool_value : ErrorBool -> Value
| string_value : ErrorString -> Value.


Scheme Equality for Value.

(* Definition Env := string -> Value.
Definition env : Env := fun x => undeclared. *)


Definition check_eq_over_types (t1 : Value) (t2 : Value) : bool :=
  match t1 with
    | undeclared => match t2 with 
                     | undeclared => true
                     | _ => false
                     end
    | default => match t2 with 
                  | default => true
                  | _ => false
                  end
    | err_assign => match t2 with 
                  | err_assign => true
                  | _ => false
                  end
    | nat_value _x => match t2 with
                  | nat_value _x => true
                  | _ => false
                  end
    | bool_value _x => match t2 with 
                  | bool_value _x => true
                  | _ => false
                  end
    | string_value  _x => match t2 with
                  | string_value _x => true
                  | _ => false
                  end
  end.

(* Definition update (env : Env) (x : string) (v : Value) : Env :=
  fun y =>
    if (eqb y x)
    then
       if(andb (check_eq_over_types undeclared (env y)) (negb (check_eq_over_types default v)))
       then undeclared
       else if((check_eq_over_types undeclared (env y)))
            then default
            else if(orb (check_eq_over_types default (env y)) (check_eq_over_types v (env y)))
                 then v
                  else err_assign
    else (env y). *)

(*  Notation "S [ V /' X ]" := (update S X V) (at level 20). *)

(* Definition Memory := nat -> Value. *)
(* Arithmetic expressions *)

 Inductive AExp :=
| avar : string -> AExp
| anum : ErrorNat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.


Coercion avar : string >-> AExp.
Coercion anum : ErrorNat >-> AExp.
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

Notation "A <' B" := (blessthan A B) (at level 72).
Notation "A >' B" := (bgreaterthan A B) (at level 70).
Notation "! A" := (bnot A)(at level 50).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 80).


(* String operations*)

Inductive StringExp :=
| svar : string -> StringExp
| sstring : ErrorString -> StringExp
| concat: ErrorString -> ErrorString -> StringExp
| compare: ErrorString -> ErrorString -> StringExp
| Slength: ErrorString -> StringExp.

Coercion svar: string >->StringExp.
Notation " A += B " := (concat A B) (at level 60).

Check "ana" += "maria".

Inductive pointer :=
| nullptr : pointer
| ptr : string -> pointer
| ref : string -> pointer.

(* in C un pointer poate fi asignat/declarat doar cu trei tipuri de valori: un alt pointer, referinta unei variabile
sau NULL*)
Notation " A **" := (ptr A)(at level 20).
Notation "&& A" := (ref A )(at level 20).
Check "a"**.
Check &&"a".

(*Statements*)
Require Import Coq.Lists.List.
Import ListNotations.



Inductive Stmt :=
| nat_decl : string -> AExp -> Stmt
| bool_decl : string -> BExp -> Stmt
| string_decl : string -> StringExp -> Stmt
| array_decl :  string -> nat -> Stmt
| pointer_decl : Set -> string -> pointer -> Stmt
| reference_decl : Set -> string -> string -> Stmt
| nat_assign : string -> AExp -> Stmt
| bool_assign : string -> BExp -> Stmt
| string_assign : string -> StringExp -> Stmt
| pointer_assign : string -> pointer -> Stmt
| reference_assign : string -> string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt->Stmt
| switch : AExp -> list cases -> Stmt
| functionCall: string -> list string -> Stmt
| struct : list Members -> Stmt
with cases  :=
| case : AExp -> Stmt -> cases
| defaultcase: Stmt->cases
with Members :=
| member : Type -> string -> Value -> Members.
(* ^ only one list in switch???*)

(* OR *)(* 
Inductive cases :=
| case : AExp -> Stmt -> cases
| defaultCase : Stmt -> cases.

Inductive switch :=
| switchCase: AExp -> list cases -> switch.
 *)

Notation "A [[ B ]]" := (array_decl  A B) (at level 58).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 98).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "'Nat'' X ::= A" := (nat_decl X A)(at level 90).
Notation "'Bool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'Stringg' X ::= A" := (string_decl X A)(at level 92).
Notation "F  {{ A }}  " :=  (functionCall F A)(at level 88).

Check pointer_decl nat "a" nullptr.
Check pointer_decl nat "a" ("b" **).
Check pointer_decl nat "a" (&& "b").
Check  "a"[[10]].
Check "a" :n= 0.
Check Nat' "a" ::= 0.
Check Stringg "a" ::=  "ana".
Check ifthen (3<'2) ("a" :n= 3).
Check 1+'2.
Check "func" {{["a"]}}.

Check switch (1+'2) [ defaultcase ("a" :n= 5)].
Check switch (avar "a")
    [case (5) ("a" :n= 4);
     defaultcase ("a" :n= 0)].

(*Arrays*)

(* ++declare arrays??? *)
Definition Array:= nat -> Value.

Definition array0 : Array :=
  fun x =>
    if (Nat.eqb x 0)
    then nat_value 10
    else  nat_value 0.

Compute array0 0.
Compute array0 1.

Inductive ArrayOp :=
| Alength : Array -> ArrayOp
| push: Array -> Value -> ArrayOp
| delete: Array -> nat -> ArrayOp
| pop: Array -> ArrayOp.

Check Alength array0.


(* Struct *)
Compute struct [member nat "a" default].
Compute struct [member bool "b" (bool_value true); 
                member nat "x" (default)].


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


Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. (* offset which indicates the current number of memory zones *)

Scheme Equality for Mem.

(* Environment *)
Definition Env := string -> Mem.

(* Memory Layer *)
Definition MemLayer := Mem -> Value.

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Env -> MemLayer -> Stack -> Config.

(* Function for updating the environment *)
Definition update_env (env: Env) (x: string) (n: Mem) : Env :=
  fun y =>
      (* If the variable has assigned a default memory zone, 
         then it will be updated with the current memory offset *)
      if (andb (string_beq x y ) (Mem_beq (env y) mem_default))
      then
        n
      else
        (env y).

Definition env : Env := fun x => mem_default.

(* Initially each variable is assigned to a default memory zone *)
Compute (env "z"). (* The variable is not yet declared *)

(* Example of updating the environment, based on a specific memory offset *)
Compute (update_env env "x" (offset 9)) "x".

(* Function for updating the memory layer *)
Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Mem) (v : Value) : MemLayer :=
  fun y => 
      if(andb (Mem_beq (env x) type) (Mem_beq y type))
      then
        if(andb(check_eq_over_types undeclared (mem y)) (negb(check_eq_over_types default v)))
        then undeclared
        else if (check_eq_over_types undeclared (mem y))
            then default
            else if(orb(check_eq_over_types default (mem y)) (check_eq_over_types v (mem y)))
                 then v
                 else err_assign
      else (mem y).
(* Each variable/function name is initially mapped to undeclared *)
Definition mem : MemLayer := fun x => undeclared.

Check "n" :n= 10 ;;
      "ok" :b= btrue ;;
      "i" :n= 0 ;;
      "msg" :s= "Hello" ;;
      struct [member bool "b" (bool_value true); 
                member nat "x" (default)];;
      "func" {{["a"]}};;
      switch (avar "a")
     [case (5) ("a" :n= 4);
     defaultcase ("a" :n= 0)];;
      while ("i" <' "n" +' 1) (
            "s" :n= "s" +' 1 ;;
            "i" :n= "i" +' 1
      ).

(* Definition update_conf (c:config) (n:nat) (env:Env) : config :=
   Pay attention!!! In order to be able to monitor the state of the entire program, you need to
   implement a function "update_conf", which updates the 
   entire configuration (environment, memory layout and stack).  
   config : nat -> Env -> MemLayer -> Stack -> Config (the first value represents the last memory zone, 
   and you will need to find a way to increment it each time a new variable/function is declared)
*)

(* Functions / global/local variables *)
(*
  - Restructurare program: declaratii de variabile / declaratii de functii
  - In Stmt trebuie adaugat si apelul de functii (care este sintaxa?)
  - Liste de argumente pentru functii: List type.
  - Atentie la sintaxa!!!
  - Referinte/pointeri: lucrul cu zona de memorie
  - Vectori: de asigurat ca se pot pastra n zone de memorie in functie de dimensiunea vectorului.
*)

