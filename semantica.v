Load sintaxa.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Bool.Bool.


(*SEMANTICS*)

Check bool.
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

Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. (* offset which indicates the current number of memory zones *)

Scheme Equality for Mem.

(* Environment *)
Definition Env := string -> Mem.

(* Memory Layer *)
Definition MemLayer := Mem -> Value.

(*  Notation "S [ V /' X ]" := (update S X V) (at level 20). *)

(* Definition Memory := nat -> Value. *)

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  | config : nat -> Env -> MemLayer -> Stack -> Config.


Definition env : Env := fun x => mem_default.
Definition mem : MemLayer := fun x => undeclared.
Definition stack : Stack := [env].
Definition getEmptyEnv: Env := fun x => mem_default.
Definition env1 : Env :=
  fun x =>
    if(String.eqb "n" x)
    then offset 1
    else if(String.eqb "sum" x)
            then offset 0
            else if(String.eqb "boolean" x)
                    then offset 2
                    else if (String.eqb "string" x)
                         then offset 3
                         else if(String.eqb "vector" x)
                              then offset 4
                              else if (String.eqb "suma" x)
                                   then offset 5
                              else mem_default.
Compute env1 "boolean".
Definition mem1 : MemLayer :=
  fun x => 
        if (Mem_beq x (offset 0))
        then (nat_value 0)
        else if(Mem_beq x (offset 1))
             then (nat_value 4)
             else if(Mem_beq x (offset 2))
                then (bool_value false)
                else if(Mem_beq x (offset 3))
                     then (string_value "plp")
                     else if(Mem_beq x (offset 4))
                          then (array_value ("vector" [[10]]->n [1;2;3]))
                          else if(Mem_beq x (offset 5))
                               then (code (Nat' "sum" ::= 0;;"sum" :n= "sum" +' "n"))
                     else undeclared.



Definition FunctionEnv := string -> list types.
Definition StructEnv := string -> list members.
Definition functionEnv : FunctionEnv :=
  fun x => [].
Definition functionEnv1 : FunctionEnv :=
  fun x => if(String.eqb "suma" x)
           then [naturalT "n"]
           else [].
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
(* Pay attention!!! In order to be able to monitor the state of the entire program, you need to
   implement a function "update_conf", which updates the 
   entire configuration (environment, memory layout and stack).  
   config : nat -> Env -> MemLayer -> Stack -> Config (the first value represents the last memory zone, 
   and you will need to find a way to increment it each time a new variable/function is declared)
*)

(* Definition update_conf_nat (n:nat) (c:Config) : Config :=
  match c with
  | config n' e m s => config (n+n') e m s
  end.  *)

Definition update_conf (n:nat) (env : Env) (mem:MemLayer) (s:Stack) (c:Config) : Config :=
  match c with
  | config a b c d => config (n+a) env mem (env :: d)
  end.

Compute update_conf 1 env mem stack.


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

Notation "S [ V /e X ]" := (update_env S X V) (at level 10). 

(* Initially each variable is assigned to a default memory zone *)
Compute (env "z"). (* The variable is not yet declared *)
Compute mem (env "z").
Compute mem (offset 0).

(* Example of updating the environment, based on a specific memory offset *)
Compute (update_env env "x" (offset 9)) "x".

(* Function for updating the memory layer *)
Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Mem) (v : Value) : MemLayer :=
  fun y => 
      if(andb (Mem_beq (env x) type) (Mem_beq y type))
      then
        if (andb (check_eq_over_types undeclared (mem y)) (check_eq_over_types default v))
            then default
            else  v
      else (mem y).
Notation "S { V /m X } \ M \ T" := (update_mem M S V T X)(at level 10).
Check env [ (offset 4) /e "a" ].
Check env {"a" /m (nat_value 10)}\mem\(mem_default).

(*AEXP SEMANTICS*)


Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition min_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
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

Definition length_ErrorString (s : ErrorString) : ErrorNat :=
  match s with
  | error_string => error_nat
  | String s1 => String.length (s1)
  end.

Fixpoint aeval_fun (a : AExp) (env : Env) (mem:MemLayer) : ErrorNat :=
  match a with
  | avar v => match (mem (env v)) with
                | nat_value n => n
                | _ => error_nat
                end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env mem) (aeval_fun a2 env mem))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env mem) (aeval_fun a2 env mem))
  | amin a1 a2 => (min_ErrorNat (aeval_fun a1 env mem) (aeval_fun a2 env mem))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env mem) (aeval_fun a2 env mem))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env mem) (aeval_fun a2 env mem))
  | slength s => length_ErrorString s
  end.


Reserved Notation "A ` M =[ S ]=> N" (at level 30).

Inductive aeval : AExp -> Env -> MemLayer -> ErrorNat -> Prop :=
| const : forall n sigma mem' , anum n ` mem' =[ sigma ]=> n 
| var : forall v sigma mem' ,avar v ` mem' =[ sigma ]=>  match (mem' (sigma v)) with
                                                     | nat_value _x => _x
                                                     | _ => error_nat
                                                      end
| add : forall a1 a2 i1 i2 sigma n,
    a1 ` mem=[ sigma ]=> i1 ->
    a2 ` mem =[ sigma ]=> i2 ->
    n = (plus_ErrorNat i1 i2) ->
    (a1 +' a2) ` mem =[sigma]=> n
| diff: forall a1 a2 i1 i2 sigma n,
    a1 ` mem =[ sigma ]=> i1 ->
    a2 ` mem =[ sigma ]=> i2 ->
    n = (min_ErrorNat i1 i2) ->
    (a1 -' a2) ` mem=[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 ` mem =[ sigma ]=> i1 ->
    a2 ` mem =[ sigma ]=> i2 ->
    n = (mul_ErrorNat i1 i2) ->
    (a1 *' a2) ` mem =[sigma]=> n
| div : forall a1 a2 i1 i2 sigma n,
    a1 ` mem=[ sigma ]=> i1 ->
    a2 ` mem=[ sigma ]=> i2 ->
    n = (div_ErrorNat i1 i2) ->
    (a1 /' a2) ` mem =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 ` mem=[ sigma ]=> i1 ->
    a2 ` mem=[ sigma ]=> i2 ->
    n = (mod_ErrorNat i1 i2) ->
    (a1 %' a2) ` mem=[sigma]=> n
| Length : forall s n sigma,
    n =   (length_ErrorString s) ->
    (slength s) ` mem =[sigma]=> n
where "a ` mem =[ sigma ]=> n" := (aeval a sigma mem n).


Example division_error : (12 /' 0) ` mem =[ env ]=> error_nat.
Proof.
  eapply div.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example diff1 : (13 -' 5) ` mem =[ env ]=> 8.
Proof.
  eapply diff.
  -apply const.
  -apply const.
  -simpl. reflexivity.
Qed.

Example length: (slength "ana") ` mem =[ env ]=> 3.
Proof.
  eapply Length.
  -simpl;reflexivity.
Qed.


(* BEXP SEMANTICS *)


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
    | num v1, num v2 => boolean (negb (Nat.ltb v1 v2))
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
Compute String.prefix "am" "ana".
Definition isPrefix_ErrorBool (s1 s2: ErrorString) : ErrorBool :=
  match s1, s2 with
    | error_string, _ => error_bool
    | _, error_string => error_bool
    | String s1, String s2 => String.prefix s1 s2
  end.

 Fixpoint beval_fun (a : BExp) (envnat : Env) (mem : MemLayer) : ErrorBool :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => error_bool
  | bvar v => match mem(env v) with
                |  bool_value n => n
                | _ => error_bool
                end
  | blessthan a1 a2 => (lt_ErrorBool (aeval_fun a1 envnat mem) (aeval_fun a2 envnat mem))
  | bgreaterthan a1 a2 => (gt_ErrorBool (aeval_fun a1 envnat mem ) (aeval_fun a2 envnat mem))
  | bnot b1 => (not_ErrorBool (beval_fun b1 envnat mem))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 envnat mem) (beval_fun b2 envnat mem))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 envnat mem) (beval_fun b2 envnat mem))
  | isPrefix s1 s2 => (isPrefix_ErrorBool s1 s2)
  end. 

Reserved Notation "B ~' M ={ S }=> B'" (at level 20).
Inductive beval : BExp -> Env -> ErrorBool -> MemLayer -> Prop :=
| b_error: forall sigma mem, berror ~' mem ={ sigma }=> error_bool
| b_true : forall sigma mem, btrue ~' mem ={ sigma }=> true
| b_false : forall sigma mem, bfalse  ~' mem ={ sigma }=>   false
| b_var : forall v sigma mem', bvar v  ~' mem' ={ sigma }=>   match mem'(sigma v) with
                                                | bool_value x => x
                                                | _ => error_bool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b mem,
    a1 ` mem =[ sigma ]=> i1 ->
    a2 ` mem =[ sigma ]=> i2 ->
    b = (lt_ErrorBool i1 i2) ->
    (a1 <' a2)  ~' mem ={ sigma }=>   b
| b_not : forall a1 i1 sigma b mem,
    a1 ~' mem ={ sigma }=> i1 ->
    b = (not_ErrorBool i1) ->
    (!'a1)  ~' mem ={ sigma }=>   b 
| b_and : forall a1 a2 i1 i2 sigma b,
    a1  ~' mem ={ sigma }=> i1 ->
    a2  ~' mem ={ sigma }=> i2 ->
    b = (and_ErrorBool i1 i2) ->
    (a1 and' a2)  ~' mem ={ sigma }=>  b
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ~' mem ={ sigma }=> i1 ->
    a2 ~' mem ={ sigma }=> i2 ->
    b = (or_ErrorBool i1 i2) ->
    (a1 or' a2)  ~' mem ={ sigma }=>  b 
| is_prefix : forall s1 s2 b sigma,
    b = (isPrefix_ErrorBool s1 s2) ->
    isPrefix s1 s2 ~' mem ={ sigma }=> b
where "B ~' M ={ S }=> B'" := (beval B S B' M).

Example prefix1: (isPrefix "ana" "anamaria") ~' mem ={ env }=> true.
Proof.
  eapply is_prefix.
  -simpl;reflexivity.
Qed.

Example and1: (btrue and' bfalse) ~' mem ={ env }=> false.
Proof.
  eapply b_and.
  -eapply b_true.
  -eapply b_false.
  -simpl;reflexivity.
Qed.

Example not: (!' (bvar "boolean")) ~' mem1 ={ env1 }=> true.
Proof.
  eapply b_not.
  - eapply b_var.
  - simpl;reflexivity.
Qed.

(* STRING OPERATIONS SEMANTICS *)

Definition concat_ErrorString (s1 s2 : ErrorString ) : ErrorString :=
  match s1, s2 with 
  | error_string,_ => error_string
  | _,error_string => error_string
  | String s1, String s2 => String (append s1 s2)
  end.

Definition areEqual_ErrorString (s1 s2 : ErrorString) : ErrorString :=
  match s1, s2 with
  | error_string,_ => error_string
  | _,error_string => error_string
  | String s1, String s2 => if (String.eqb s1 s2 )
                            then s1
                            else String (EmptyString)
  end.

 Definition substring_ErrorString (s1 : ErrorString) (n m:nat) : ErrorString :=
  match s1 with
  | error_string => error_string  
  | String s1 =>  (String.substring n m s1)
  end.

 Fixpoint seval_fun (s:StringExp)(env:Env)(mem:MemLayer) : ErrorString :=
  match s with
  | svar s1 => match (mem(env s1)) with
              | string_value a => a
              | _ => error_string
               end
  | sstring s1 => s1
  | strcat s1 s2 => (concat_ErrorString (seval_fun s1 env mem) (seval_fun s2 env mem)) 
  | areEqual s1 s2 => (areEqual_ErrorString (seval_fun s1 env mem) (seval_fun s2 env mem))
  | substring s n m => (substring_ErrorString (seval_fun s env mem) n m)
  end.
 
Inductive seval: StringExp -> Env -> MemLayer -> ErrorString -> Prop :=
| Svar: forall s sigma mem', seval (svar s) sigma mem'  (match (mem'(sigma s)) with
                                                                     | string_value s => s
                                                                     | _ => error_string
                                                                      end)
| Sstring: forall s sigma mem, seval (sstring s) sigma mem s
| Strcat: forall s1 s2 s i1 i2 sigma mem, 
    seval s1 sigma mem i1 ->
    seval s2 sigma mem i2 ->
    s = (concat_ErrorString i1 i2) ->
    seval (strcat s1 s2) sigma mem s
| SareEqual: forall s1 s2 s i1 i2 sigma mem,
    seval s1 sigma mem i1 ->
    seval s2 sigma mem i2 ->
    s = (areEqual_ErrorString i1 i2) ->
    seval (areEqual s1 s2) sigma mem s
| Substring: forall s1 i1 s n m sigma mem,
    seval s1 sigma mem i1 ->
    s = (substring_ErrorString i1 n m ) ->
    seval (substring s1 n m) sigma mem s.

Example string_var : seval (svar "string") env1 mem1 ("plp").
Proof.
  eapply Svar.
Qed.

Example concate: seval (strcat (sstring "ana") (svar "string")) env1 mem1 ("anaplp").
Proof.
  eapply Strcat.
  - eapply Sstring.
  - eapply Svar.
  - eauto.
Qed.

Example equality: seval (areEqual (sstring "ana") (svar "string")) env1 mem1 "".
Proof.
  eapply SareEqual.
  - eapply Sstring.
  - eapply Svar.
  - simpl;reflexivity.
Qed.

(* ARRAYEXP SEMANTICS *)

Definition getElementFromArray (a:Array) (nr:nat) : Value :=
match a with
| array_nat s n l => nat_value (nth nr l 0)  
| array_bool s n l => bool_value (nth nr l false) 
| array_string s n l =>string_value (nth nr l "") 
| error_array => undeclared
end.


Definition getLastElementFromArray (a:Array) : Value :=
match a with 
| array_nat s n l => nat_value (List.last l 0)
| array_bool s n l => bool_value (List.last l false)
| array_string s n l => string_value (List.last l "")
| error_array => undeclared
end.

Definition deleteFromArray (a:Array) (nr:nat) : Value :=
match a with
| array_nat s n l => array_value(array_nat s n (List.remove eq_nat_dec (nth nr l 0) l))
| array_bool s n l => array_value(array_bool s n (List.remove bool_dec (nth nr l false) l))
| array_string s n l =>array_value(array_string s n (List.remove string_dec (nth nr l "") l))
| error_array => undeclared
end.

Definition insertIntoArrayNat (a:Array) (nr:nat) : Value:=
match a with
| array_nat s n l => array_value (array_nat s n ([nr]++l))
| array_bool s n l => array_value a
| array_string s n l => array_value a
| error_array => undeclared
end.

Definition insertIntoArrayBool (a:Array) (b:bool) : Value:=
match a with
| array_nat s n l => array_value a
| array_bool s n l => array_value (array_bool s n ([b]++l))
| array_string s n l => array_value a
| error_array => undeclared
end.

Definition insertIntoArrayString (a:Array) (str:string) : Value :=
match a with
| array_nat s n l => array_value a
| array_bool s n l => array_value a
| array_string s n l => array_value (array_string s n ([str]++l))
| error_array => undeclared
end.

Inductive array_eval: ArrayExp -> Env -> MemLayer -> Value -> Prop :=
| arr_Const: forall arr sigma mem, array_eval (arr_const arr) sigma mem (array_value arr)
| arr_Var: forall arr sigma mem, array_eval (arr_var arr) sigma mem  (mem(sigma arr))
| arr_elementAt: forall arr nr sigma mem, array_eval (elementAt arr nr) sigma mem (getElementFromArray arr nr)
| arr_first: forall arr sigma mem, array_eval (first arr) sigma mem (getElementFromArray arr 0)
| arr_last: forall arr sigma mem, array_eval (last arr) sigma mem (getLastElementFromArray arr) 
| arr_deleteAt: forall arr nr sigma mem, array_eval (deleteAt arr nr) sigma mem (deleteFromArray arr nr)
| arr_insertNat: forall arr nr sigma mem, array_eval (insertNat arr nr) sigma mem (insertIntoArrayNat arr nr)
| arr_insertBool: forall arr b sigma mem, array_eval (insertBool arr b) sigma mem (insertIntoArrayBool arr b)
| arr_insertString: forall arr str sigma mem, array_eval (insertString arr str) sigma mem (insertIntoArrayString arr str).



Example variable_arr: array_eval (arr_var "vector") env1 mem1 (array_value ("vector" [[10]]->n [1;2;3])).
Proof.
  eapply arr_Var.
Qed.

Example firstelement: array_eval (first ("a"[[10]]->n [1;2;3])) env1 mem1 (nat_value 1) .
Proof.
  eapply arr_first.
Qed.

Example element: array_eval (elementAt("a"[[10]]->n [1;2;3]) 1) env1 mem1 (nat_value 2).
Proof.
  eapply arr_elementAt.
Qed.

(* LISTS SEMANTICS *)

Inductive list_eval: ListOp -> Env -> MemLayer -> ListTypes -> Prop :=
| list_const: forall l sigma mem, list_eval (List l) sigma mem l
| list_var: forall s l sigma mem, list_eval (listvar s l) sigma mem l
| list_begin': forall l sigma l' mem,
  list_eval l sigma mem l' ->
  list_eval (begin l) sigma mem match l' with
                                | natList list_nat => natList ([(nth 0 list_nat 0)])
                                | boolList list_bool =>boolList ([ nth 0 list_bool false])
                                | stringList list_string =>stringList([ nth 0 list_string ""])
                                end
| list_end: forall l sigma l' mem ls,
  list_eval l sigma mem l' ->
  ls = (match l' with
                              | natList list_nat => natList([List.last list_nat 0])
                              | boolList list_bool => boolList ([List.last list_bool false])
                              | stringList list_string => stringList ([List.last list_string ""])
                              end) ->
  list_eval (l.End()) sigma mem ls
| list_pushBack: forall el l l' sigma mem ls, 
  list_eval l sigma mem l' ->
  ls =  match l' with
                              | natList list_nat => match el with
                                                   | natElm n => natList (rev (n :: (rev list_nat)))
                                                   | boolElm b => natList list_nat
                                                   | stringElm s => natList list_nat
                                                    end
                              | boolList list_bool => match el with 
                                                   | natElm n =>boolList list_bool
                                                   | boolElm b => boolList (b::list_bool)
                                                   | stringElm s =>boolList list_bool
                                                   end
                              | stringList list_string => match el with
                                                       | natElm n => stringList list_string
                                                       | boolElm b => stringList list_string
                                                       | stringElm s => stringList (s :: list_string)
                                                         end
                              end ->
  list_eval (l.push_back(el)) sigma mem ls
| list_pushFront: forall el l l' sigma mem ls, 
  list_eval l sigma mem l' ->
  ls = match l' with
                              | natList list_nat => match el with
                                                   | natElm n => natList ([n]++ list_nat)
                                                   | boolElm b => natList list_nat
                                                   | stringElm s => natList list_nat
                                                    end
                              | boolList list_bool => match el with 
                                                   | natElm n =>boolList list_bool
                                                   | boolElm b => boolList ([b]++list_bool)
                                                   | stringElm s =>boolList list_bool
                                                   end
                              | stringList list_string => match el with
                                                       | natElm n => stringList list_string
                                                       | boolElm b => stringList list_string
                                                       | stringElm s => stringList ([s] ++ list_string)
                                                         end
                              end ->
  list_eval (l.push_front(el)) sigma mem ls 
| list_popFront: forall l l' sigma mem ls,
  list_eval l sigma mem l' ->
  ls = match l' with
                                 | natList list_nat => natList (List.remove eq_nat_dec (nth 0 list_nat 0) list_nat)
                                 | boolList list_bool =>boolList (List.remove bool_dec (nth 0 list_bool false) list_bool)
                                 | stringList list_string => stringList (List.remove string_dec (nth 0 list_string "") list_string)
                                  end ->
  list_eval (pop_front l) sigma mem ls
| list_popBack: forall l l' sigma mem ls,
  list_eval l sigma mem l' ->
  ls =  match l' with
                                 | natList list_nat => natList (List.removelast  list_nat)
                                 | boolList list_bool =>boolList (List.removelast  list_bool)
                                 | stringList list_string => stringList (List.removelast  list_string)
                                  end ->
  list_eval (pop_back l) sigma mem ls.

Example list_fin: list_eval (((l->n [1;2;3]) <op>).End()) env1 mem1 (natList ([3])).
Proof.
  eapply list_end.
  - eapply list_const.
  - simpl; eauto.
Qed.
 
Example pushBack: list_eval(((l->n [1;2;3]) <op>).push_back(natElm 4)) env1 mem1 (natList ([1;2;3;4])).
Proof.
  eapply list_pushBack.
  -eapply list_const.
  -simpl;eauto.
Qed.

Example popFront: list_eval(((l->n [1;2;3]) <op>).pop_front()) env1 mem1 (natList ([2;3])).
Proof.
  eapply list_popFront.
  -eapply list_const.
  -eauto.
Qed.


(*STATEMENTS SEMANTICS*)

(* How to update a variable ???
--> For every variable you have to assign a memory zone
--> For every memory zone you can assign a value
So, to update a variable first you have to give the variable a memory zone (you can get the
last memory zone from Config) and using that memory zone you properly assign a value to the 
variable. So the steps for assigning the variabile s with the value v are:
1. Assign the first free memory zone to the variable s using update_env. Let's say that the variable
v is assigned at the n offset.
2. At the offset n memory zone you have to assign the value v, using update_mem.
3. Update the configuration ( the last memory zone is changed, also the environment and the memory).
*)
(* Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Mem) (v : Value) : MemLayer := *)
Definition declare_variable (c:Config) (s:string) (v:Value) :Config :=
match c with
| config Last env mem stack => config (Last+1) env (update_mem mem (update_env env s (offset (Last+1)))
s (offset (Last +1)) v ) (update_env env s (offset (Last+1)) :: (List.removelast stack))
end.

Definition declare_array (c:Config) (a:Array)  : Config :=
match c with
| config Last env mem stack => match a with 
                              | array_nat s n lNat => config (Last+n) env (update_mem mem 
                              (update_env env s (offset(Last+1))) s (offset (Last + 1)) (array_value a) ) 
                              ((update_env env s (offset(Last+1))) :: (List.removelast stack))
                              | array_bool s n lNat => config (Last+n) env (update_mem mem 
                              (update_env env s (offset(Last+1))) s (offset (Last + 1)) (array_value a) ) 
                              ((update_env env s (offset(Last+1))) :: (List.removelast stack))
                              | array_string s n lNat => config (Last+n) env (update_mem mem 
                              (update_env env s (offset(Last+1))) s (offset (Last + 1)) (array_value a) ) 
                              ((update_env env s (offset(Last+1))) :: (List.removelast stack))
                              | error_array => c
                              end
end.

Definition declare_reference (c:Config) (s1 s2 : string) : Config :=
match c with
| config Last env mem stack => config Last env mem ((update_env env s2 (env s1)) :: (List.removelast stack))
end.

(* has to be modified *)
Definition declare_pointer (c:Config) (s:string) (p:pointer) :Config :=
match c with
| config Last env mem stack => config Last env mem ((update_env env s match p with
                                                            | nullptr => mem_default
                                                            | ptr s =>  (env s)
                                                            | ref s =>  (env s)
                                                           end )::(List.removelast stack))
end.

Definition declare_struct (c:Config) (s1 s2: string) : Config :=
match c with
| config Last env' mem' stack => config (Last+1) env' (update_mem mem' (update_env env' s2 (offset (Last+1)))
s2 (offset (Last +1)) default ) ((update_env env' s2 (offset (Last+1))) :: (List.removelast stack)) 
end.


Definition getFromConfigEnv (c:Config) : Env :=
match c with
| config a b c d => nth 0 d b
end.

Definition getFromConfigMemZone (c:Config) : nat :=
match c with
| config a b c d => a
end.

Definition getFromConfigMem (c:Config) : MemLayer :=
match c with 
| config a b c d => c
end.

Definition getFromConfigStack (c:Config) : Stack :=
match c with 
| config a b c d => d
end. 

Definition update_variable (c:Config) (s:string) (v:Value) : Config :=
match c with 
| config Last env' mem' stack => if(Mem_beq ((getFromConfigEnv c) s) mem_default)
                                    then config Last env' (update_mem mem' env' s (env' s) v) stack 
                                    else config Last env' (update_mem mem' (getFromConfigEnv c) s ((getFromConfigEnv c) s) v) stack 
end.

Definition print_variable (c:Config) (s:string) : Value :=
match c with
| config Last env mem stack => mem( (nth 0 stack env) s)
end.

Compute print_variable (update_variable (config 2 env1 mem1 [env1]) "n" (nat_value 10)) "n".

Definition update_pointer (c:Config) (s:string) (p:pointer) :Config := 
match c with
| config Last env mem stack => config Last env mem ((update_env env s match p with
                                                            | nullptr => mem_default
                                                            | ptr s =>  (env s)
                                                            | ref s =>  (env s)
                                                           end )::(List.removelast stack))
end.
Fixpoint execute_switch (a:ErrorNat) (l:list cases) : Stmt :=
 match l with
  | nil => error_stmt
  | el::l' => match el with
              | (case aexp stmt) => if(ErrorNat_beq (aeval_fun aexp env mem) a) then stmt else (execute_switch  a l')
              | defaultcase stmt => stmt
              end                           
end.
Compute execute_switch 5 ([case 2 ("a" :n=10); defaultcase ("a" :n= 2)]).
Compute functionEnv1 "suma".
Compute nth 0 (functionEnv1 "suma") error_types.
Compute print_variable (config 0 env1 mem1 [env1]) "suma".
Fixpoint addParametersToEnv (c:Config)(fnc:string)(l: list parameters) (nr : nat)(functionEnv':FunctionEnv) : Config :=
 match l with
 | nil => c
 | el::l' => match c with
            | config Last env mem stack => match el with
                                          | error_param => c
                                          | nat_param n => match (nth nr (functionEnv' fnc) error_types) with
                                                           | error_types => c
                                                           | naturalT s => addParametersToEnv (declare_variable c s (nat_value n)) fnc l' (nr+1) functionEnv'
                                                           | booleanT s => c
                                                           | StringT s => c
                                                            end
                                          | bool_param n =>  match (nth nr (functionEnv' fnc) error_types) with
                                                           | error_types => c
                                                           | naturalT s => c
                                                           | booleanT s => addParametersToEnv (declare_variable c s (bool_value n)) fnc l' (nr+1) functionEnv'
                                                           | StringT s => c
                                                            end
                                          | string_param n =>  match (nth nr (functionEnv' fnc) error_types) with
                                                           | error_types => c
                                                           | naturalT s => c
                                                           | booleanT s => c
                                                           | StringT s => addParametersToEnv (declare_variable c s (string_value n)) fnc l' (nr+1) functionEnv'
                                                            end
                                          | variable s => c
                                         end
            end
 end.

Definition updateConfig (c:Config) (env:Env) : Config :=
match c with
| config a b c d => config (a+1) env c (env :: d)
end.

Definition getFunctionBody (c:Config) (s:string) : Stmt :=
match c with
| config last_m env' mem' stack => match mem'(env' s) with
                                | code stmt => stmt
                                | _ => error_stmt
                                end
end.




Compute hd (getFromConfigStack (updateConfig (config 0 env1 mem [env1]) (env))).
Compute  (declare_variable (config 0 env mem [env]) "a" (nat_value 10)) .

Fixpoint eval_fun (s : Stmt) (gas: nat) (config' :Config) (fnc:FunctionEnv) : Config :=
    match gas with
    | 0 => config'
    | S gas' => match s with
                | error_stmt => config'
                | sequence S1 S2 => eval_fun S2 gas' (eval_fun S1 gas' config' fnc) fnc
                | nat_decl a aexp => declare_variable config' a (nat_value (aeval_fun aexp (getFromConfigEnv config') (getFromConfigMem config'))) 
                | bool_decl b bexp => declare_variable config' b (bool_value (beval_fun bexp (getFromConfigEnv config') (getFromConfigMem config'))) 
                | string_decl s StringExp => declare_variable config' s (string_value (seval_fun StringExp (getFromConfigEnv config') (getFromConfigMem config'))) 
                | array_decl a => declare_array config' a
                | reference_decl s s' => declare_reference config' s s'
                | pointer_decl s s' => declare_pointer config' s s'
                | list_decl s l => declare_variable config' s ( list_value l) 
                | struct_decl s s' => declare_struct config' s s' 
                | nat_assign s a => update_variable config' s (nat_value (aeval_fun a (getFromConfigEnv config') (getFromConfigMem config')))
                | bool_assign s b => update_variable config' s (bool_value (beval_fun b (getFromConfigEnv config') (getFromConfigMem config')))
                | string_assign s a => update_variable config' s (string_value (seval_fun a (getFromConfigEnv config') (getFromConfigMem config')))
                | pointer_assign s p => update_pointer config' s p
                | reference_assign s a => declare_reference config' s a
                | ifthen b s => config'
                | ifthenelse b s1 s2 => config'
                | while b s => config'
                | For s1 b s2 s3 => config'
                | switch a l => config'
                | functionCall s l => eval_fun (getFunctionBody config' s) gas' (addParametersToEnv config'  s l 0 fnc) fnc
              end    
end.


Compute print_variable (eval_fun (Nat' "a" ::= 5) 10 (config 0 env mem stack) functionEnv) ("a").
Compute print_variable (eval_fun (Bool "b" ::= bfalse) 10 (config 0 env mem stack) functionEnv) "b".
Compute print_variable (eval_fun (Stringg "s" ::= sstring "ana") 10 (config 0 env mem stack) functionEnv) "s".
Compute print_variable (eval_fun (Array'::="a"[[10]]->n [1;2]) 10 (config 0 env mem stack) functionEnv) "a".
Compute print_variable (eval_fun ("a" ::p= "n"**) 10 (config 0 env1 mem1 [env1]) functionEnv)"a".
Compute print_variable (eval_fun ("List" ::l= (l->n [1;2;3;4])<op>) 10 (config 0 env mem stack ) functionEnv) ("List").

Compute functionEnv1 "suma".
Compute print_variable (config 0 env1 mem1 [env1]) "suma".
Compute print_variable (eval_fun  ("suma" {{[nat_param 8]}}) 10 (config 0 env1 mem1 [env1]) functionEnv1) "sum". 
Inductive eval : Stmt  -> Config -> Config -> FunctionEnv -> StructEnv ->Prop := 
| e_error: forall sigma sigma' fnc str, eval (error_stmt) sigma sigma' fnc str
| e_nat_decl: forall s i a  sigma sigma' fnc str,
   a ` (getFromConfigMem sigma)=[ (getFromConfigEnv sigma) ]=> i ->
   sigma' = declare_variable sigma s (nat_value i) ->
   eval (Nat' s ::= a) sigma sigma' fnc str
| e_bool_decl: forall s i b sigma sigma' fnc str,
   b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> i ->
   sigma' = declare_variable sigma s (bool_value i) ->
   eval (Bool s ::= b) sigma sigma' fnc str
| e_string_decl: forall s i s' sigma sigma' fnc str,
   seval s' (getFromConfigEnv sigma) (getFromConfigMem sigma) i ->
   sigma' = declare_variable sigma s (string_value i) ->
   eval (Stringg s ::= s') sigma sigma fnc str
| e_array_decl: forall arr sigma sigma' fnc str,
  sigma' = (declare_array sigma  arr) ->
  eval (Array'::= arr) sigma sigma' fnc str
| e_reference_decl: forall s s' sigma sigma' fnc str,
  sigma' = (declare_reference sigma s s') ->
  eval (s ::r= s') sigma sigma' fnc str
| e_pointer_decl : forall s s' sigma sigma' fnc str,
  sigma' = (declare_pointer sigma s s') ->
  eval (s ::p= s') sigma sigma' fnc str
| e_list_decl : forall s l sigma sigma' fnc str,
  sigma' = ( declare_variable sigma s (list_value l)) ->
  eval (s ::l= l )  sigma  sigma' fnc str
| e_struct_decl : forall s s' sigma sigma' fnc str,
  sigma' = (declare_struct sigma s s') ->
  eval (struct_decl s s') sigma sigma' fnc str
| e_nat_assign: forall a i s sigma sigma' fnc str,
  a ` (getFromConfigMem sigma)=[ (getFromConfigEnv sigma) ]=> i ->
  sigma' = (update_variable sigma s (nat_value i)) ->
  eval (s :n= a)  sigma sigma' fnc str
| e_bool_assign: forall b i s sigma sigma' fnc str,
  b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> i ->
  sigma' = update_variable sigma s (bool_value i) ->
  eval ( s :b= b) sigma sigma' fnc str
| e_string_assign: forall s i s' sigma sigma' fnc str,
   seval s' (getFromConfigEnv sigma) (getFromConfigMem sigma) i ->
   sigma' = update_variable sigma s (string_value i) ->
   eval (s :s= s') sigma sigma' fnc str
| e_pointer_assign : forall s s' sigma sigma' fnc str,
  sigma' = (update_pointer sigma s s') ->
  eval (s :p= s') sigma sigma' fnc str
| e_reference_assign: forall s s' sigma sigma' fnc str,
  sigma' = (declare_reference sigma s s') ->
  eval (s :r= s') sigma sigma' fnc str
| e_seq : forall s1 s2 sigma sigma1 sigma2 fnc str,
    eval s1 sigma  sigma1 fnc str->
    eval s2  sigma1  sigma2 fnc str->
    eval (s1 ;; s2) sigma sigma2 fnc str
| e_iffalse : forall b s sigma fnc str,
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> false ->
    eval (ifthen b s) sigma sigma fnc str
| e_iftrue : forall b s sigma sigma1 fnc str,
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> true ->
    eval s sigma  sigma1 fnc str ->
    eval (ifthen b s) sigma sigma1 fnc str
| e_ifthenfalse : forall b s1 s2 sigma sigma1 fnc str,
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> false ->
    eval s2 sigma  sigma1 fnc str->
    eval (ifthenelse b s1 s2) sigma sigma1 fnc str
| e_ifthentrue : forall b s1 s2 sigma sigma1 fnc str,
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> true ->
    eval s1 sigma  sigma1 fnc str->
    eval (ifthenelse b s1 s2) sigma sigma1 fnc str
| e_whilefalse : forall b s sigma fnc str,
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> false ->
    eval (while b s) sigma  sigma fnc str
| e_whiletrue : forall b s sigma sigma' fnc str,
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> true ->
    eval (s ;; while b s)  sigma  sigma' fnc str->
    eval (while b s) sigma  sigma' fnc str
| e_fortrue: forall s1 b s2 s3 sigma sigma1 sigma2 fnc str,
    eval s1 sigma  sigma1 fnc str->
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> true ->
    eval (while b (s2;;s3)) sigma1 sigma2 fnc str->
    eval (For s1 b s2 s3 ) sigma  sigma2 fnc str
| e_forfalse: forall s1 b s2 s3 sigma sigma1 fnc str,
    eval s1 sigma sigma1 fnc str->
    b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> true ->
    eval (while b (s2;;s3)) sigma1 sigma1 fnc str ->
    eval (For s1 b s2 s3 ) sigma  sigma1 fnc str
| e_switch: forall s a l i sigma sigma' fnc str,
    a ` (getFromConfigMem sigma)=[ (getFromConfigEnv sigma) ]=> i ->
    s = execute_switch i l ->
    eval s  sigma sigma' fnc str ->
    eval (switch a l)  sigma  sigma' fnc str
| e_functionCall_1: forall s l stmt sigma sigma' fnc str,
    stmt = getFunctionBody sigma s ->
    eval stmt sigma sigma' fnc str -> 
    eval (functionCall s l) sigma sigma' fnc str
.

(* Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Mem) (v : Value) : MemLayer := *)

Require Import Omega.
Example if_true : eval (If  "n" <' 12 Then  "n" :n= 3 Else "n":n=10 End) (config 0 env1 mem1 [env1]) (config 0 env1 (env1 {"n" /m nat_value 3}\ mem1 \ (env1 "n")) [env1]) functionEnv structEnv.
Proof.
  eapply e_ifthentrue.
  -simpl;eapply b_lessthan;eauto.
    + eapply var.
    + eapply const.
    + simpl;eauto.
  -eapply e_nat_assign.
    + eapply const.
    + eauto.
Qed.

Example assign_nat: eval ("n" :n= 5) (config 0 env1 mem1 [env1]) (config 0 env1 (env1 {"n" /m nat_value 5}\ mem1 \ (env1 "n")) [env1]) functionEnv structEnv.
Proof.
  eapply e_nat_assign.
  -eapply const.
  - simpl;eauto.
Qed.
 
Example var_decl: eval (Nat' "n" ::= 10) (config 0 env1 mem1 [env1]) (config 1 env1 ((env1 [offset 1 /e "n"]) {"n" /m nat_value 10}\ mem1 \ (offset 1))  [env1 [offset 1 /e "n"]]) functionEnv structEnv.
Proof.
  eapply e_nat_decl.
  - simpl.
    +eapply const.
  - simpl;eauto.
Qed.

Example switch_exec: eval (switch (avar "n") [case (4) (Nat' "a" ::=4); defaultcase (Nat' "a" ::= 10)]) (config 0 env1 mem1 [env1] ) (config 1 env1 ((env1 [offset 1 /e "a"]) {"a" /m nat_value 4}\ mem1 \ (offset 1))  [env1 [offset 1 /e "a"]]) functionEnv structEnv.
Proof.
  eapply e_switch.
  -simpl; eapply var.
  -simpl;eauto.
  -eapply e_nat_decl.
    +simpl; eapply const.
    +eauto.
Qed.

Definition declare_variableGlobal (c:Config) (s:string) (v:Value) :Config :=
match c with
| config Last env mem stack => config (Last+1) (update_env env s (offset (Last+1))) (update_mem mem (update_env env s (offset (Last+1)))
s (offset (Last +1)) v ) (update_env env s (offset (Last+1)) :: (List.removelast stack))
end.

Inductive program_eval : program -> Config -> Config -> FunctionEnv -> StructEnv -> Prop :=
| p_seq: forall s1 s2 sigma sigma1 sigma2 fnc str,
    program_eval s1 sigma sigma1 fnc str->
    program_eval s2 sigma1 sigma2 fnc str->
    program_eval (s1 ;;; s2) sigma sigma2 fnc str
| p_declNat: forall s i a  sigma sigma' fnc str,
   a ` (getFromConfigMem sigma)=[ (getFromConfigEnv sigma) ]=> i ->
   sigma' = declare_variableGlobal sigma s (nat_value i) ->
   program_eval (Nat_gl s ::n= a) sigma sigma' fnc str
| p_declBool: forall s i b  sigma sigma' fnc str,
   b ~' (getFromConfigMem sigma) ={ getFromConfigEnv sigma }=> i ->
   sigma' = declare_variableGlobal sigma s (bool_value i) ->
   program_eval (Bool_gl s ::b= b) sigma sigma' fnc str
| p_declString: forall s i s'  sigma sigma' fnc str,
   seval s' (getFromConfigEnv sigma) (getFromConfigMem sigma) i ->
   sigma' = declare_variableGlobal sigma s (string_value i) ->
   program_eval (String_gl s ::s= s') sigma sigma' fnc str
| p_declFunction: forall s l c sigma sigma' functionEnv' fnc str,
   sigma' = (declare_variableGlobal sigma s (code c)) ->
   functionEnv' = update_FunctionEnv fnc s l ->
   program_eval (function s l (code c)) sigma sigma' functionEnv' str
| p_declStruct: forall s l sigma  structEnv fnc str,
   structEnv = update_StructEnv str s l ->
   program_eval (struct s l) sigma sigma fnc structEnv
| p_main : forall s sigma sigma' fnc str,
   eval s sigma sigma' fnc str ->
   program_eval (main s) sigma sigma' fnc str.

Example declarare: program_eval (Nat_gl "a" ::n= 10) (config 0 env mem stack) (config 1 (env [offset 1 /e "a"]) ((env [offset 1 /e "a"]) {"a" /m nat_value 10}\ mem \(offset 1)) [env [offset 1 /e "a"]]) functionEnv structEnv.
Proof.
  eapply p_declNat.
  -eapply const.
  -simpl;eauto.
Qed.

Example func: program_eval (function "suma" [naturalT "a"]
  (
   code(
     "sum" :n= "sum" +' "n"
  )
  )) (config 0 env1 mem1 [env1]) (config 1 (env1 [offset 1 /e "suma"])
  ((env1 [offset 1 /e "suma"]) {"suma" /m
   code ("sum" :n= "sum" +' "n")}\ mem1 \ 
   (offset 1)) [env1 [offset 1 /e "suma"]]) (update_FunctionEnv functionEnv "suma" [naturalT "a"]) structEnv.

Proof.
  eapply p_declFunction.
  -simpl;eauto.
  -eauto.
Qed.


Definition prg2 := 
  (Nat_gl "sum" ::n= 0) ;;;
 (struct "pereche"
  [
    member "stanga" default_nat;
    member "dreapta" default_nat
  ]);;;
  function "main" [naturalT "a"]
  (
   code(
     "sum" :n= "sum" +' "n";;
     struct_decl "pereche" "p1"
  )
  ) 
.


Example program1: program_eval (prg2) (config 0 (env) mem[env])
  (config 2 ((env [offset 1 /e "sum"]) [offset 2 /e "main"])(((env [offset 1 /e "sum"]) [offset 2 /e "main"]) {"main" /mcode ("sum" :n= "sum" +' "n";; struct_decl "pereche" "p1")}\(env [offset 1 /e "sum"]) {"sum" /m nat_value 0}\ mem \ (offset 1) \ (offset 2)) [(env [offset 1 /e "sum"]) [offset 2 /e "main"]])
 ((update_FunctionEnv functionEnv "main" [naturalT "a"]))
  (update_StructEnv structEnv "pereche" [
    member "stanga" default_nat;
    member "dreapta" default_nat
  ]).
Proof.
  eapply p_seq.
  -eapply p_seq.
   + eapply p_declNat.
       ++ eapply const.
       ++ simpl;eauto.
    +eapply p_declStruct.
      ++simpl;eauto.
-eapply p_declFunction.
  +simpl;eauto. 
  +eauto.
Qed.




