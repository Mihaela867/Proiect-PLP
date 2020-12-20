Load proiect.


(*SEMANTICS*)

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
        if(andb(check_eq_over_types undeclared (mem y)) (negb(check_eq_over_types default v)))
        then undeclared
        else if (andb (check_eq_over_types undeclared (mem y)) (check_eq_over_types default v))
            then default
            else if(orb(check_eq_over_types default (mem y)) (check_eq_over_types v (mem y)))
                 then v
                 else err_assign
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

(* Fixpoint aeval_fun (a : AExp) (env : Env) (mem:MemLayer) : ErrorNat :=
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
  end.
 *)

Reserved Notation "A ` M =[ S ]=> N" (at level 30).

Inductive aeval : AExp -> Env -> MemLayer -> ErrorNat -> Prop :=
| const : forall n sigma mem , anum n ` mem =[ sigma ]=> n (* <n,sigma> => <n> *) 
| var : forall v sigma mem ,avar v ` mem =[ sigma ]=>  match (mem (sigma v)) with
                                                     | nat_value x => x
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

(* Fixpoint beval_fun (a : BExp) (envnat : Env) (mem : MemLayer) : ErrorBool :=
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
  end. *)

Reserved Notation "B ~' M ={ S }=> B'" (at level 20).
Inductive beval : BExp -> Env -> ErrorBool -> MemLayer -> Prop :=
| b_error: forall sigma mem, berror ~' mem ={ sigma }=> error_bool
| b_true : forall sigma mem, btrue ~' mem ={ sigma }=> true
| b_false : forall sigma mem, bfalse  ~' mem ={ sigma }=>   false
| b_var : forall v sigma mem, bvar v  ~' mem ={ sigma }=>   match mem(sigma v) with
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
where "B ~' M ={ S }=> B'" := (beval B S B' M).

(* add examples *)


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
  | String s1, String s2 => if (eqb s1 s2 )
                            then s1
                            else String (EmptyString)
  end.

(* Definition substring_ErrorString (s1 : ErrorString) (n m:AExp) : StringExp :=
  match s1 with
  | error_string =>sstring error_string  
  | String s1 =>  (substring s1 n m)
  end. *)

(* Fixpoint seval_fun (s:StringExp)(env:Env)(mem:MemLayer) : ErrorString :=
  match s with
  | svar s1 => match (mem(env s1)) with
              | string_value a => a
              | _ => error_string
               end
  | sstring s1 => s1
  | strcat s1 s2 => (concat_ErrorString (seval_fun s1 env mem) (seval_fun s2 env mem)) 
  | areEqual s1 s2 => (areEqual_ErrorString (seval_fun s1 env mem) (seval_fun s2 env mem))
  end.
 *)
(* 
Inductive seval: StringExp -> Env -> MemLayer -> ErrorString -> Prop :=
| Svar: forall s sigma mem, seval (svar s) sigma mem s
| Sstring: forall s sigma mem, seval (sstring s) sigma mem match(mem(sigma s)) with
                                                          | string_value s => s
                                                          | _ => error_string
                                                          end.

 *)

(*STATEMENTS SEMANTICS*)


Definition getFromConfigEnv (c:Config) : Env :=
match c with
| config a b c d => b
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


(* Fixpoint eval_fun (s : Stmt) (gas: nat) (config' :Config) : Config :=
    match gas with
    | 0 => config'
    | S gas' => match s with
                | sequence S1 S2 => eval_fun S2 gas' (eval_fun S1 gas' config') 
                | nat_decl a aexp => update_conf 1 (update_env (getFromConfigEnv config') a (offset (getFromConfigMemZone config'))) (update_mem (getFromConfigMem config') (getFromConfigEnv config') a (offset(getFromConfigMemZone config')) ((nat_value (aeval_fun aexp env (getFromConfigMem config')))))(getFromConfigStack config') config'
                | bool_decl b bexp => config'
                | string_decl s StringExp => config'
                | array_decl s n => config'
                | array_decl_list_nat s n l => config'
                | array_decl_list_bool s n l => config'
| array_decl_list_string s n l => config'
| pointer_decl_nat s p => config'
| pointer_decl_bool s p => config'
| reference_decl s s' => config'
| nat_assign s a => config'
| bool_assign s b => config'
| string_assign s a => config'
| pointer_assign s p => config'
| reference_assign s a => config'
| array_elm_assign_nat a n => config'
| array_elm_assign_bool a b => config'
| array_elm_assign_string a s => config'
| ifthen b s => config'
| ifthenelse b s1 s2 => config'
| while b s => config'
| For s1 b s2 s3 => config'
| switch a l => config'
| functionCall s l => config'

              end    
end.


Compute (eval_fun ("a" :n= 5) 10 (config 1 env mem stack)(getFromConfigEnv (eval_fun ("a" :n= 5) 10 (config 1 env mem stack)) "a")).
 

Reserved Notation "S \ C -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Env -> Config -> Env -> Prop :=
| e_nat_decl: forall a i x c sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   (x :n= a) -{ sigma }-> sigma' *)
(* 
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (res_nat i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (res_bool i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma' 
where "s \ config -{ sigma }-> sigma'" := (eval s sigma config sigma').*)

