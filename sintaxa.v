(*SYNTAX*)

(*Variables and environment*)


Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.
Require Import Coq.Lists.List.
Import ListNotations.
Scheme Equality for list.

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
Scheme Equality for ErrorNat.
Scheme Equality for ErrorString.
Scheme Equality for ErrorBool.

(* Arithmetic expressions *)

 Inductive AExp :=
| avar : string -> AExp
| anum : ErrorNat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| slength: ErrorString -> AExp.


Coercion avar : string >-> AExp.
Coercion anum : ErrorNat >-> AExp.
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (amin A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "len( A )" := (slength A) (at level 50, left associativity).

(* Boolean expressions *)

Inductive BExp :=
| berror: BExp
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| isPrefix: ErrorString -> ErrorString -> BExp.

Notation "A <' B" := (blessthan A B) (at level 72).
Notation "A >' B" := (bgreaterthan A B) (at level 70).
Notation "!' A" := (bnot A)(at level 50).
Infix "and'" := band (at level 80).
Infix "or'" := bor (at level 80).

(* String operations*)

 Inductive StringExp :=
| svar : string -> StringExp
| sstring : ErrorString -> StringExp
| strcat: StringExp -> StringExp -> StringExp
| areEqual: StringExp -> StringExp -> StringExp
| substring: StringExp -> nat -> nat -> StringExp.


Coercion svar: string >->StringExp.
Notation " A += B " := (strcat A B) (at level 60). 

Notation "A /in B" := (substring A B)(at level 55).


Check "ana" += "maria". 



(* pointers and references*)

Inductive pointer := 
| nullptr : pointer
| ptr : string -> pointer
| ref : string -> pointer.
Scheme Equality for pointer.
(* In c++ references are an alternative name for the same variable, and a pointer is a variable that,
instead of data, it stores adresses *)
(* in C un pointer poate fi asignat/declarat doar cu trei tipuri de valori: un alt pointer, referinta unei variabile
sau NULL*)
Notation " A **" := (ptr A)(at level 20).
Notation "&& A" := (ref A )(at level 20).
Check "a"**.
Check &&"a".

(*Arrays*)

Inductive Array :=
| error_array
| array_nat : string ->nat -> list nat -> Array
| array_bool : string -> nat -> list bool -> Array
| array_string : string -> nat -> list string -> Array.

Notation "A [[ N ]]->n B  " := (array_nat A N B) (at level 50).
Notation "A [[ N ]]->b B " := (array_bool A N B) (at level 50).
Notation "A [[ N ]]->s B  " := (array_string A N B) (at level 50).

Check "a"[[10]]->n [ 1;2;3].

Inductive ArrayExp :=
| arr_const: Array->ArrayExp
| arr_var: string -> ArrayExp
| elementAt : Array -> nat ->ArrayExp
| first: Array -> ArrayExp
| last: Array -> ArrayExp 
| deleteAt: Array -> nat -> ArrayExp
| insertNat: Array  -> nat -> ArrayExp
| insertBool: Array  -> bool -> ArrayExp
| insertString: Array  -> string -> ArrayExp.

Notation " s [[' i ']] " := (elementAt s i)(at level 22).

Check ("a"[[10]]->n [1;2;3])[['1']].

(* List Operations *)

Inductive ListTypes :=
| natList: list nat -> ListTypes
| boolList: list bool -> ListTypes
| stringList: list string -> ListTypes.

Notation "l->n A" := (natList A)(at level 38).
Notation "l->b A" := (boolList A)(at level 38).
Notation "l->s A" := (stringList A)(at level 38).
Check l->n [1;2;3].
Check l->b [true;false].
Check l->s ["mama";"tata"].

Inductive ListElmType :=
| natElm : nat -> ListElmType
| boolElm : bool -> ListElmType
| stringElm : string -> ListElmType.

Coercion natElm: nat >-> ListElmType.
Coercion boolElm: bool >-> ListElmType.
Coercion stringElm: string >-> ListElmType.

Inductive ListOp :=
| List : ListTypes -> ListOp
| listvar : string -> ListTypes -> ListOp
| begin : ListOp -> ListOp
| End' : ListOp -> ListOp
| push_front : ListOp -> ListElmType -> ListOp
| push_back : ListOp -> ListElmType -> ListOp
| pop_front : ListOp -> ListOp
| pop_back : ListOp -> ListOp.

Notation "A <op>" := (List A) (at level 36).
Notation "A .begin()" := (begin A) (at level 50).
Notation "A .End()" := (End' A) (at level 50).
Notation "A .push_front( B )" := (push_front A B) (at level 50).
Notation "A .push_back( B )" := (push_front A B) (at level 50).
Notation "A .pop_front()" := (pop_front A) (at level 50).
Notation "A .pop_back()" := (pop_back A) (at level 50).
Check (l->n [1;2;3]) <op>.
Check ((l->n [1;2;3]) <op>).begin().
Check ((l->n [1;2;3]) <op>).End().
Check ((l->n [1;2;3]) <op>).push_back(natElm 1).




(*Statements*)

Inductive Stmt :=
| error_stmt
| nat_decl : string -> AExp -> Stmt
| bool_decl : string -> BExp -> Stmt
| string_decl : string -> StringExp -> Stmt
| array_decl : Array  -> Stmt
| pointer_decl: string -> pointer -> Stmt
| reference_decl : string -> string -> Stmt
| list_decl : string -> ListOp -> Stmt
| struct_decl : string -> string -> Stmt
| nat_assign : string -> AExp -> Stmt
| bool_assign : string -> BExp -> Stmt
| string_assign : string -> StringExp -> Stmt
| pointer_assign : string -> pointer -> Stmt
| reference_assign : string -> string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| switch : AExp -> list cases -> Stmt
| functionCall: string -> list parameters -> Stmt
with cases  :=
| case : AExp -> Stmt -> cases
| defaultcase: Stmt -> cases
with parameters :=
| error_param
| nat_param :  ErrorNat -> parameters
| bool_param : ErrorBool -> parameters
| string_param : ErrorString -> parameters
| variable : string -> parameters.


Notation "'Nat'' X ::= A" := (nat_decl X A)(at level 90).
Notation "'Bool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'Stringg' X ::= A" := (string_decl X A)(at level 92).
Notation "Array'::= A" := (array_decl A ) (at level 58). 
Notation "A ::p= B" := (pointer_decl A B) (at level 59).
Notation "A ::r= B" := (reference_decl A B) (at level 50).
Notation "A ::l= B" := (list_decl A B) (at level 60).
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "X :p= A" := (pointer_assign X A)(at level 80).
Notation "X :r= A" := (reference_assign X A)(at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 98).
Notation "'If' B 'Then' S1 'End'" := (ifthen B S1) (at level 97).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).
Notation "'For(' S1 ';' B ';' S2 ')' '{' S3 '}'" := (For S1 B S2 S3)(at level 88).
Notation "F  {{ A }}  " :=  (functionCall F A)(at level 88).

Check "a" ::p= nullptr.
Check "a" ::p= ("b" **).
Check "a" ::p= (&& "b").
Check "list1" ::l= (l->n [1;2;3]) <op>.
Check "a" :n= 0.
Check Nat' "a" ::= 0.
Check Stringg "a" ::=  "ana".
Check If "b">'2 Then "a" ::p= &&"b" End.
Check If "b">'2 Then "a" ::p= &&"b" Else "a" ::p= nullptr End.
Check For("a":n=0 ; "a"<'10 ; "a" :n= "a" +' 1)
{
   "s" :n= "s" +' "a"
 }.
Check "a" :p= nullptr.
Check Array'::= "a" [[10]]->n [1;2].
Check "func" {{[variable "a"]}}.
Check switch (1+'2) [ defaultcase ("a" :n= 5)].
Check switch (avar "a")
    [case (5) ("a" :n= 4);
     defaultcase ("a" :n= 0)].
Compute  nth 1 [case (5) ("a" :n= 4); defaultcase ("a" :n= 0)].
Compute List.last (rev [1;2;3]).

Inductive types :=
| error_types
| naturalT: string -> types
| booleanT: string -> types
| StringT: string -> types.

Inductive Value:=
| undeclared : Value
| default : Value
| default_nat : Value
| default_bool : Value
| default_string : Value
| err_assign : Value
| nat_value : ErrorNat -> Value
| bool_value : ErrorBool -> Value
| string_value : ErrorString -> Value
| array_value: Array -> Value
| list_value: ListOp -> Value
| code : Stmt -> Value.


Definition Value_equality (t1 : Value) (t2 : Value) : bool :=
  match t1 with
    | undeclared => match t2 with 
                     | undeclared => true
                     | _ => false
                     end
    | default => match t2 with 
                  | default => true
                  | _ => false
                  end
    | default_nat => match t2 with
                  | default => true
                  | _ => false
                  end
    | default_bool => match t2 with
                  | default_bool => true
                  | _ => false
                  end
    | default_string => match t2 with
                  | default_string => true
                  | _ => false
                  end
    | err_assign => match t2 with 
                  | err_assign => true
                  | _ => false
                  end
    | nat_value a => match t2 with
                  | nat_value b => if (ErrorNat_beq a b) then true else false
                  | _ => false
                  end
    | bool_value a => match t2 with 
                  | bool_value b => if (ErrorBool_beq a b) then true else false
                  | _ => false
                  end
    | string_value  a => match t2 with
                  | string_value b => if (ErrorString_beq a b) then true else false
                  | _ => false
                  end
    | array_value  _x => match t2 with
                  | array_value _x => true
                  | _ => false
                  end
    | list_value  _x => match t2 with
                  | list_value _x => true
                  | _ => false
                  end
    | code _x => match t2 with
                  | code _x => true
                  | _ => false
                 end
  end. 

Check code ("a" :n= 0).
Inductive  members :=
| member: string -> Value -> members.

Definition FunctionEnv := string -> list types.
Definition StructEnv := string -> list members.
Definition functionEnv : FunctionEnv :=
  fun x => [].
Definition structEnv : StructEnv :=
  fun x => [].
Definition update_FunctionEnv (fnc_env:FunctionEnv) (s:string) (l:list types) : FunctionEnv :=
 fun x => 
     if (string_beq s x) then l
     else (fnc_env x).

Definition update_StructEnv (st_env:StructEnv) (s:string) (l:list members) :StructEnv :=
  fun x =>
      if (string_beq s x) then l
      else (st_env x).
(* Program *)

Inductive program :=
| Seq_prg: program -> program -> program
| decl_globalNat : string -> AExp -> program
| decl_globalBool : string -> BExp -> program
| decl_globalString : string -> StringExp -> program
| function: string -> list types -> Value -> program
| struct : string -> list members -> program
| main: Stmt ->program.

Notation " A ;;; B " := (Seq_prg A B)(at level 20).
Notation "'Nat_gl' A ::n= B" := (decl_globalNat A B)(at level 30).
Notation "'Bool_gl' A ::b= B" := (decl_globalBool A B)(at level 30).
Notation "'String_gl' A ::s= B" := (decl_globalString A B)(at level 30).
(* Notation "'func' A '(' B ')' '{(' C ')}' 'end_func'" := (function A B C)(at level 30). *)

Check main ("a" :n= 10) ;;; function "f1" [naturalT "a"] (code ("a" :n=10)).
Check Nat_gl "a" ::n= 10.
Check Bool_gl "b" ::b= btrue.
Check String_gl "s" ::s= "start"%string.


Check "n" :n= 10 ;;
      "ok" :b= btrue ;;
      "i" :n= 0 ;;
      "msg" :s= "Hello" ;;

      "func" {{[variable "a"]}};;
      switch (avar "a")
     [case (5) ("a" :n= 4);
     defaultcase ("a" :n= 0)];;
      while ("i" <' "n" +' 1) (
            "s" :n= "s" +' 1 ;;
            "i" :n= "i" +' 1
      ).

Definition prg := 
  (Nat_gl "sum" ::n= 0) ;;;
  function "suma" [naturalT "a"]
  (
   code(
    For("i":n=0 ; "i"<'"a" ; "i" :n= "i" +' 1)
    {
     "sum" :n= "sum" +' "a"
    }
  )
  ) ;;;
  (struct "pereche"
  [
    member "stanga" default_nat;
    member "dreapta" default_nat
  ]);;;

  main 
      (Nat' "a" ::= 10 ;;
      "ok" :b= btrue ;;
      "i" :n= 0 ;;
      "msg" :s= "Hello" ;;
      "nume" :s= "Ana" += "Maria" ;;
      "suma" {{[variable "a"]}};;
      switch (avar "a")
     [case (5) ("a" :n= 4);
     defaultcase ("a" :n= 0)];;
      while ("i" <' "n" +' 1) (
            "s" :n= "s" +' 1 ;;
            "i" :n= "i" +' 1
      )
).
Compute prg.


