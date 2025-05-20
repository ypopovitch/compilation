Require Import String.
Require Import List.
Require Import Arith.
Import ListNotations.
 
Inductive YExpr :=
    | YConst : nat -> YExpr
    | YVar : string -> YExpr
    | YAdd : YExpr -> YExpr -> YExpr
    | YMul : YExpr -> YExpr -> YExpr.
 
Inductive YStmt :=
    | YSkip
    | YAssign : string -> YExpr -> YStmt
    | YSeq : YStmt -> YStmt -> YStmt.
 
Inductive XExpr :=
    | XConst : nat -> XExpr
    | XAdrs : string -> XExpr.
 
Inductive XInstr :=
    | XAdd : XInstr
    | XMul : XInstr
    | XLoadConst : nat -> XInstr
    | XLoadAdrs : string -> XInstr
    | XStore : string -> XInstr.
 
Definition XProgram := list XInstr.
Definition XStack := list nat.
Definition empty_xprog : list XInstr := nil.
Definition empty_stack : list nat := nil.
 
(* Env definitions *)
 
Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=  (fun _ => v).
Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) := 
  fun x' => if String.eqb x x' then v else m x'.
  
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
  
Notation "x '!->' v ';' m" := (t_update m x v)
 (at level 100, v at next level, right associativity).

Definition Env := total_map (option nat).

Definition empty_env : Env :=  t_empty None.

Definition update_env (m : Env) (x : string) (n : nat) :=  (x !-> Some n ; m).
 
Notation "x '⊢>' v ';' m" := (update_env m x v) (at level 100, v at next level, right associativity).
 
Notation "x '⊢>' v" := (update_env empty_env x v) (at level 100).
  
Example example_env := "a" ⊢> 3 ; "c" ⊢> 6.

(* compilation *)
 
Fixpoint compile_expr (yexpr : YExpr) (xprog : XProgram) :=
  match yexpr with
  | YConst n => XLoadConst n :: xprog
  | YVar s => XLoadAdrs s :: xprog
  | YAdd yexpr1 yexpr2 => compile_expr yexpr1 (compile_expr yexpr2 (XAdd :: xprog))
  | YMul yexpr1 yexpr2 => compile_expr yexpr1 (compile_expr yexpr2 (XMul :: xprog))
  end.
 
Fixpoint compile (yprog : YStmt) (xprog : XProgram) :=
  match yprog with
  | YSkip => xprog
  | YAssign s yexpr => (compile_expr yexpr nil) ++ [XStore s] ++ xprog
  | YSeq stmt1 stmt2 => compile stmt1 (compile stmt2 xprog)
  end.

(* small and big step semantics *)
 
Inductive YStep_expr (env : Env) : YExpr -> YExpr -> Prop :=
  | YStep_Var : forall (s : string) (n : nat) (H : env s = Some n),
    YStep_expr env (YVar s) (YConst n)
  | YStep_Add1 : forall (yexpr1 yexpr1' yexpr2 : YExpr),
    (YStep_expr env yexpr1 yexpr1') ->
    YStep_expr env (YAdd yexpr1 yexpr2) (YAdd yexpr1' yexpr2)
  | YStep_Add2 : forall (n1 : nat) (yexpr2 yexpr2' : YExpr),
    (YStep_expr env yexpr2 yexpr2') ->
    YStep_expr env (YAdd (YConst n1) yexpr2) (YAdd (YConst n1) yexpr2')
  | YStep_Add3 : forall (n1 n2 : nat),
    YStep_expr env (YAdd (YConst n1) (YConst n2)) (YConst (n1 + n2))
  | YStep_Mul1 : forall (yexpr1 yexpr1' yexpr2 : YExpr),
    (YStep_expr env yexpr1 yexpr1') ->
    YStep_expr env (YMul yexpr1 yexpr2) (YMul yexpr1' yexpr2)
  | YStep_Mul2 : forall (n1 : nat) (yexpr2 yexpr2' : YExpr),
    (YStep_expr env yexpr2 yexpr2') ->
    YStep_expr env (YMul (YConst n1) yexpr2) (YMul (YConst n1) yexpr2')
  | YStep_Mul : forall (n1 n2 : nat),
    YStep_expr env (YMul (YConst n1) (YConst n2)) (YConst (n1 * n2)).
 
Inductive YStep : (YStmt * Env) -> (YStmt * Env) -> Prop :=
  | YStep_Skip : forall (env : Env) (yprog : YStmt),
    YStep (YSeq YSkip yprog, env) (yprog, env)
  | YStep_Assgn1 : forall (env : Env) (yprog : YStmt) (s : string) (yexpr yexpr': YExpr),
    YStep_expr env yexpr yexpr' ->
    YStep (YSeq (YAssign s yexpr) yprog, env) (YSeq (YAssign s yexpr') yprog, env)
  | YStep_Assgn2 : forall (env : Env) (yprog : YStmt) (s : string) (n : nat),
    YStep (YSeq (YAssign s (YConst n)) yprog, env) (yprog, s ⊢> n ; env).
 
Inductive XExec : (XProgram * XStack * Env) -> (XProgram * XStack * Env) -> Prop :=
  | XEx_Self : forall (xprog : XProgram) (stack : XStack) (env : Env),
     XExec (xprog, stack, env) (xprog, stack, env)
  | XEx_LoadC : forall (xprog : XProgram) (stack : XStack) (env : Env) (n : nat),
    XExec ((XLoadConst n) :: xprog, stack, env) (xprog, n :: stack, env)
  | XEx_LoadV : forall (xprog : XProgram) (stack : XStack) (env : Env)
    (str : string ) (n : nat) (H : env str = Some n),
    XExec ((XLoadAdrs str) :: xprog, stack, env) (xprog, n :: stack, env)
  | XEx_Store : forall (xprog : XProgram) (stack : XStack) (env : Env)
    (str : string ) (n : nat),
    XExec ((XStore str) :: xprog, n :: stack, env) (xprog, stack, str ⊢> n ; env)
  | XExec_Add : forall (xprog : XProgram) (stack : XStack) (env : Env) (n1 n2 : nat),
    XExec (XAdd :: xprog, n1 :: n2 :: stack, env) (xprog, (n1 + n2) :: stack, env)
  | XExec_Mul : forall (xprog : XProgram) (stack : XStack) (env : Env) (n1 n2 : nat),
    XExec (XMul :: xprog, n1 :: n2 :: stack, env) (xprog, (n1 * n2) :: stack, env).

Inductive YMultiStep_expr (env : Env) : YExpr -> YExpr -> Prop :=
  | YMultiStep_expr_smallStep : forall (yexpr1 yexpr2 : YExpr),
    YStep_expr env yexpr1 yexpr2 -> YMultiStep_expr env yexpr1 yexpr2
  | YMultiStep_expr_trans : forall (yexpr1 yexpr2 yexpr3 : YExpr),
    YMultiStep_expr env yexpr1 yexpr2 -> YMultiStep_expr env yexpr2 yexpr3 ->
    YMultiStep_expr env yexpr1 yexpr3.
 
Inductive YMultiStep : (YStmt * Env) -> (YStmt * Env) -> Prop :=
  | YMultiStep_smallStep : forall (yprog1 yprog2 : YStmt) (env1 env2 : Env),
    YStep (yprog1, env1) (yprog2, env2) -> YMultiStep (yprog1, env1) (yprog2, env2)
  | YMultiStep_trans : forall (yprog1 yprog2 yprog3: YStmt) (env1 env2 env3: Env),
    YMultiStep (yprog1, env1) (yprog2, env2) ->
    YMultiStep (yprog2, env2) (yprog3, env3) ->
    YMultiStep (yprog1, env1) (yprog3, env3).
 
Inductive XMultiExec : (XProgram * XStack * Env) -> (XProgram * XStack * Env) -> Prop :=
  | XMultiExec_smallExec : forall (xprog1 xprog2 : XProgram) (stack1 stack2 : XStack) (env1 env2 : Env),
      XExec (xprog1, stack1, env1) (xprog2, stack2, env2) -> XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2)
  | XMultiExec_trans : forall (xprog1 xprog2 xprog3: XProgram) (stack1 stack2 stack3: XStack) (env1 env2 env3: Env),
      XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2) ->
      XMultiExec (xprog2, stack2, env2) (xprog3, stack3, env3) ->
      XMultiExec (xprog1, stack1, env1) (xprog3, stack3, env3).
 
Definition YisFinalStateOf (yprog1 : YStmt) (env1 env2 : Env) : Prop :=
  YMultiStep (yprog1, env1) (YSkip, env2).

Definition XisFinalStateOf (xprog1 : XProgram) (env1 env2 : Env) (stack : XStack) : Prop :=
  XMultiExec (xprog1, stack, env1) ([], [], env2).

(* proofs *)

Theorem y_expr_smallstep_is_unique : forall (yexpr1 yexpr2 yexpr3 : YExpr) (env : Env),
  YStep_expr env yexpr1 yexpr2 ->
  YStep_expr env yexpr1 yexpr3 ->
  yexpr2 = yexpr3.
Proof. Admitted.

Theorem y_expr_finalstep_is_unique : forall (yexpr : YExpr) (env : Env) (n1 n2 : nat),
  YMultiStep_expr env yexpr (YConst n1) ->
  YMultiStep_expr env yexpr (YConst n2) ->
  n1 = n2.
Proof. Admitted.

Theorem ysmallstep_is_unique : forall (yprog1 yprog2 yprog3 : YStmt) (env1 env2 env3 : Env),
   YStep (yprog1, env1) (yprog2, env2) -> 
   YStep (yprog1, env1) (yprog3, env3) ->
   (yprog2, env2) = (yprog3, env3).
Proof. Admitted.

Theorem y_finalstep_exists : forall (yprog : YStmt) (env1 : Env),
  exists env2, YisFinalStateOf yprog env1 env2.
Proof. Admitted.

Theorem y_finalstep_is_unique : forall (yprog : YStmt) (env1 env2 env3 : Env),
  YMultiStep (yprog, env1) (YSkip, env2) ->
  YMultiStep (yprog, env1) (YSkip, env3) -> 
  env2 = env3.
Proof. Admitted.

Lemma add_cannot_be_used_with_empty_stack : 
  forall (xprog1 xprog2 : XProgram) (stack : XStack) (env1 env2 : Env),
  XMultiExec (XAdd :: xprog1, empty_stack, env1)  (xprog2, stack, env2) -> False.
Proof. Admitted.

Lemma add_cannot_be_used_with_empty_stack_smallstep : 
  forall (xprog1 xprog2 : XProgram) (stack : XStack) (env1 env2 : Env),
  XExec (XAdd :: xprog1, empty_stack, env1)  (xprog2, stack, env2) -> False.
Proof. Admitted.

Lemma add_cannot_be_used_with_single_nat_smallstep : 
  forall (xprog1 xprog2 : XProgram) (stack : XStack) (env1 env2 : Env) (n : nat),
  XExec (XAdd :: xprog1, [n], env1)  (xprog2, stack, env2) -> False.
Proof. Admitted.

Theorem xexec_smallstep_is_unique : forall (xprog1 xprog2 xprog3 : XProgram)
  (stack1 stack2 stack3 : XStack) (env1 env2 env3 : Env),
  XExec (xprog1, stack1, env1) (xprog2, stack2, env2) ->
  XExec (xprog1, stack1, env1) (xprog3, stack3, env3) ->
  (xprog2, stack2, env2) = (xprog3, stack3, env3).
Proof. Admitted.

(*
  intros. induction xprog1.
  - inversion H. subst. inversion H0. subst. reflexivity.
  - destruct a.
    * destruct stack1. 
        + apply add_cannot_be_used_with_empty_stack_smallstep in H. exfalso. assumption.
        + destruct stack1.
            -- apply add_cannot_be_used_with_single_nat_smallstep in H. exfalso. assumption.
            -- Print XExec. inversion H. subst. inversion H0. subst.
                ** reflexivity.
                ** subst. apply IHxprog1.
                    ++
*)

Theorem xexec_finalstep_exists : forall (xprog : XProgram) (env1 : Env) (stack : XStack),
  exists env2, XisFinalStateOf xprog env1 env2 stack.
Proof. Admitted.

Theorem xexec_finalstep_is_unique : forall (xprog : XProgram) (env1 env2 env3 : Env) (stack : XStack),
  XMultiExec (xprog, stack, env1) (empty_xprog, empty_stack, env2) -> 
  XMultiExec (xprog, stack, env1) (empty_xprog, empty_stack, env3) ->
  env2 = env3.
Proof. Admitted.

Theorem exec_finish_with_empty_stack : forall (xprog : XProgram) (env1 env2 : Env) (stack1 stack2 : XStack),
   XExec (xprog, stack1, env1) (empty_xprog, stack2, env2) ->
  stack2 = empty_stack.
Proof. Admitted.

Theorem skip_dont_change_semantic : forall (yprog : YStmt) (env : Env),
  YisFinalStateOf YSkip empty_env env ->
  YisFinalStateOf (YSeq YSkip yprog) empty_env env /\  YisFinalStateOf (YSeq yprog YSkip) empty_env env .
Proof. Admitted.

Theorem prog_transl_is_concat_of_stmt_transl : forall (yprog1 yprog2 : YStmt) (xprog : XProgram),
  compile (YSeq yprog1 yprog2) xprog 
    = (compile yprog1 empty_xprog) ++ (compile yprog2 xprog).
Proof. Admitted.

Definition expr_semantic_preserved (yexpr : YExpr) := forall (xprog : XProgram),
  compile_expr yexpr [] = xprog ->
  forall (env : Env) (n : nat), YMultiStep_expr env yexpr (YConst n) ->
  XMultiExec (xprog, empty_stack, env) ([], [n], env).

Theorem expr_semantic_preserved_add_const_const_old : forall (n1 n2: nat) (xprog : XProgram),
  compile_expr (YAdd (YConst n1) (YConst n2)) [] = xprog ->
  forall (env : Env), YMultiStep_expr env (YAdd (YConst n1) (YConst n2)) (YConst (n1 + n2)) ->
  XMultiExec (xprog, empty_stack, env) ([], [n1 + n2], env).
Proof.
  intros.
  remember (YAdd (YConst n1) (YConst n2)) as yexpr.
  rewrite -> Heqyexpr in H. simpl in H.
  rewrite <- H. 
  apply XMultiExec_trans with [XLoadConst n2; XAdd] [n1] env.
  - apply XMultiExec_smallExec. apply XEx_LoadC.
  - apply XMultiExec_trans with [XAdd] [n2 ; n1] env.
    * apply XMultiExec_smallExec. apply XEx_LoadC.
    * apply XMultiExec_smallExec. assert (n1 + n2 = n2 + n1). { rewrite -> Nat.add_comm. reflexivity. }
      rewrite -> H1. apply XExec_Add. Qed.

Theorem expr_semantic_preserved_add_const_const : forall (n1 n2 : nat),
  expr_semantic_preserved (YAdd (YConst n1) (YConst n2)).
Proof. Admitted.

Definition semantic_preserved (yprog : YStmt) :=  forall (xprog : XProgram) (env0 env1 env2 : Env),
  compile yprog [] = xprog ->
  YisFinalStateOf yprog env0 env1 ->
  XisFinalStateOf xprog env0 env2 empty_stack ->
  env1 = env2.

Theorem semantic_preserved_by_assign : forall (str: string) (yexpr: YExpr),
  semantic_preserved (YAssign str yexpr).
Proof. Admitted.

Inductive well_defined : YStmt -> Prop  :=
  | WellDef_Skip : well_defined YSkip
  | WellDef_Assign : forall (str : string) (yexpr : YExpr), well_defined (YAssign str yexpr)
  | WellDef_Seq_Skip : forall (yprog : YStmt),
      well_defined yprog ->
      well_defined (YSeq YSkip yprog)
  | WellDef_Seq_Assign : forall (yprog : YStmt) (str : string) (yexpr : YExpr),
      well_defined yprog ->
      well_defined (YSeq (YAssign str yexpr) yprog)
.

Theorem semantic_preserved_by_skip :
  semantic_preserved YSkip.
Proof. Admitted.

Theorem y_sequence_is_like_piping_outputs : 
  forall (yprog1 yprog2 : YStmt) (env0 env1 env2 env3 : Env),
  YMultiStep (yprog1, env0) (YSkip, env1) ->
  YMultiStep (yprog2, env1) (YSkip, env2) ->
  YMultiStep (YSeq yprog1 yprog2, env0) (YSkip, env3) ->
  env2 = env3.
Proof. Admitted.

Theorem zero_step_dont_change_env : forall (xprog : XProgram) (env1 env2 : Env) (stack1 stack2 : XStack),
  XMultiExec (xprog, stack1, env1) (xprog, stack2, env2) ->
  env2 = env1 /\ stack1 = stack2.
Proof. Admitted.

Lemma add_cannot_be_used_with_one_number : 
  forall (xprog1 xprog2 : XProgram) (stack : XStack) (env1 env2 : Env) (n : nat),
  XMultiExec (XAdd :: xprog1, [n], env1)  (xprog2, stack, env2) -> False.
Proof. Admitted.

Lemma mul_cannot_be_used_with_empty_stack : 
  forall (xprog1 xprog2 : XProgram) (stack : XStack) (env1 env2 : Env),
  XMultiExec (XMul :: xprog1, empty_stack, env1)  (xprog2, stack, env2) -> False.
Proof. Admitted.

Lemma mul_cannot_be_used_with_one_number : 
  forall (xprog1 xprog2 : XProgram) (stack : XStack) (env1 env2 : Env) (n : nat),
  XMultiExec (XMul :: xprog1, [n], env1)  (xprog2, stack, env2) -> False.
Proof. Admitted.

Lemma store_cannot_be_used_with_empty_stack : 
  forall (xprog1 xprog2 : XProgram) (stack : XStack) (env1 env2 : Env) (str : string),
  XMultiExec ((XStore str) :: xprog1, empty_stack, env1)  (xprog2, stack, env2) -> False.
Proof. Admitted.

Lemma xmulti_trans : forall (xprog1 xprog2 xprog3 : XProgram) (env1 env2 env3 : Env) (stack1 stack2 stack3 : XStack) ,
  XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2) ->
  XMultiExec (xprog2, stack2, env2) (xprog3, stack3, env3) -> 
  XMultiExec (xprog1, stack1, env1) (xprog3, stack3, env3).
Proof.
  intros. apply XMultiExec_trans with xprog2 stack2 env2.
  - assumption.
  - assumption. Qed.

(*
Lemma helper8 : forall (xprog1 xprog2 xprog3 : XProgram) (env1 env2 env3 : Env) (stack1 stack2 stack3 : XStack) ,
  XMultiExec (xprog1, stack1, env1) (xprog3, stack3, env3) ->
  XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2) ->
  (XMultiExec (xprog2, stack2, env2) (xprog3, stack3, env3) \/
    XMultiExec (xprog3, stack3, env3) (xprog2, stack2, env2)).
Proof.
  Admitted.

Lemma helper9 : forall (xprog1 xprog2 xprog3 : XProgram) (env1 env2 env3 : Env) (stack1 stack2 stack3 : XStack) ,
  XMultiExec (xprog1, stack1, env1) (xprog3, stack3, env3) ->
  XMultiExec (xprog2, stack2, env2) (xprog3, stack3, env3) ->
  (XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2) \/
    XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2)).
Proof. Admitted.
*)

Lemma helper11 : forall (xprog1 xprog2 xprog3 : XProgram) (env1 env2 env3 : Env) (stack1 stack2 stack3 : XStack) ,
  XExec (xprog1, stack1, env1) (xprog2, stack2, env2) ->
  XMultiExec (xprog1, stack1, env1) (xprog3, stack3, env3) ->
  XMultiExec (xprog2, stack2, env2) (xprog3, stack3, env3).
Proof.
  intros. induction H0.
  * assert ((xprog2, stack2, env2) = (xprog4, stack4, env4)).
    { apply xexec_smallstep_is_unique with xprog0 stack0 env0.
      * assumption.
      * assumption. }
    rewrite -> H1. apply XMultiExec_smallExec. apply XEx_Self.
  * apply IHXMultiExec1 in H. apply xmulti_trans with xprog4 env4 stack4.
    + assumption.
    + assumption. Qed.

Lemma helper12 : forall (xprog1 xprog2 xprog3 : XProgram) (env1 env2 env3 : Env) (stack1 stack2 stack3 : XStack) ,
  XMultiExec (xprog1, stack1, env1) (xprog3, stack3, env3) ->
  XExec (xprog2, stack2, env2) (xprog3, stack3, env3) ->
  XMultiExec (xprog1, stack1, env1)  (xprog2, stack2, env2).
Proof. Admitted.

Lemma helper3 : forall (xprog1 xprog2 : XProgram) (env1 env2 : Env) (stack1 stack2 : XStack) (n : nat),
XMultiExec ((XLoadConst n) :: xprog1, stack1, env1) (xprog2, stack2, env2)
<->
XMultiExec (xprog1, n :: stack1, env1) (xprog2, stack2, env2).
Proof. 
  intros. split.
  - intros. assert (XMultiExec (XLoadConst n :: xprog1, stack1, env1)  (xprog1, n :: stack1, env1)).
    { apply XMultiExec_smallExec. apply XEx_LoadC. }
    apply helper11 with (XLoadConst n :: xprog1) env1 stack1 .
    * apply XEx_LoadC.
    * assumption.
  - intros. apply xmulti_trans with xprog1 env1 (n :: stack1).
    * apply XMultiExec_smallExec. apply XEx_LoadC.
    * assumption. Qed.

Lemma helper4 : forall (xprog1 xprog2 : XProgram) (env1 env2 : Env) (stack1 stack2 : XStack) (str : string) (n : nat),
(XMultiExec ((XLoadAdrs str) :: xprog1, stack1, env1) (xprog2, stack2, env2) /\ (env1 str = Some n))
<->
(XMultiExec (xprog1, n :: stack1, env1) (xprog2, stack2, env2) /\ (env1 str = Some n)) .
Proof. 
  intros. split.
  - intros. destruct H. split.
    + apply helper11 with (XLoadAdrs str :: xprog1) env1 stack1.
      * apply XEx_LoadV. assumption.
      * assumption.
    + assumption.
  - intros. destruct H. split.
    + apply xmulti_trans with xprog1 env1 (n :: stack1).
      * apply XMultiExec_smallExec. apply XEx_LoadV. assumption.
      * assumption.
    + assumption. Qed.

Lemma helper5 : forall (xprog1 xprog2 : XProgram) (env1 env2 : Env) (stack1 stack2 : XStack) (str : string) (n : nat),
XMultiExec ((XStore str) :: xprog1, n :: stack1, env1) (xprog2, stack2, env2) 
<->
XMultiExec (xprog1, stack1, str ⊢> n ; env1) (xprog2, stack2, env2).
Proof. 
  intros. split.
  - intros. apply helper11 with (XStore str :: xprog1) env1 (n :: stack1).
    * apply XEx_Store.
    * assumption.
  - intros. apply xmulti_trans with xprog1 (str ⊢> n; env1) stack1.
    * apply XMultiExec_smallExec. apply XEx_Store.
    * assumption. Qed.

Lemma helper6 : forall (xprog1 xprog2 : XProgram) (env1 env2 : Env) (stack1 stack2 : XStack) (n1 n2 : nat),
XMultiExec (XAdd :: xprog1, n1 :: n2 :: stack1, env1) (xprog2, stack2, env2) 
<->
XMultiExec (xprog1, (n1 + n2) :: stack1, env1) (xprog2, stack2, env2).
Proof. 
  intros. split.
  - intros. apply helper11 with (XAdd :: xprog1) env1 (n1 :: n2 :: stack1).
    * apply XExec_Add.
    * assumption.
  - intros. apply xmulti_trans with xprog1 env1 (n1 + n2 :: stack1).
    * apply XMultiExec_smallExec. apply XExec_Add.
    * assumption. Qed.

Lemma helper7 : forall (xprog1 xprog2 : XProgram) (env1 env2 : Env) (stack1 stack2 : XStack) (n1 n2 : nat),
XMultiExec (XMul :: xprog1, n1 :: n2 :: stack1, env1) (xprog2, stack2, env2) 
<->
XMultiExec (xprog1, (n1 * n2) :: stack1, env1) (xprog2, stack2, env2).
Proof.
  intros. split.
  - intros. apply helper11 with (XMul :: xprog1) env1 (n1 :: n2 :: stack1).
    * apply XExec_Mul.
    * assumption.
  - intros. apply xmulti_trans with xprog1 env1 (n1 * n2 :: stack1).
    * apply XMultiExec_smallExec. apply XExec_Mul.
    * assumption. Qed.

Theorem xprog_concat_is_like_piping_outputs : forall (xprog1 xprog2 : XProgram) (env0 env1 env2 : Env) (stack : XStack),
  XMultiExec (xprog1, stack, env0) ([], empty_stack, env1) ->
  XMultiExec (xprog2, empty_stack, env1) ([], empty_stack, env2) ->
  XMultiExec (xprog1 ++ xprog2, stack, env0) ([], empty_stack, env2).
Proof.
  intros. generalize dependent stack. generalize dependent env0. induction xprog1.
  - intros. inversion H.
    * inversion H2. simpl. assumption.
    * subst. simpl. apply zero_step_dont_change_env in H. destruct H. subst. assumption.
  - intros. destruct a.
    * destruct stack.
      + apply add_cannot_be_used_with_empty_stack in H. exfalso. assumption.
      + destruct stack. 
          -- apply add_cannot_be_used_with_one_number in H. exfalso. assumption.
          -- rewrite -> helper6 in H. apply (IHxprog1 env0 (n + n0 :: stack)) in H.
              rewrite <- helper6 in H. assumption.
    * destruct stack.
      + apply mul_cannot_be_used_with_empty_stack in H. exfalso. assumption.
      + destruct stack. 
          -- apply mul_cannot_be_used_with_one_number in H. exfalso. assumption.
          -- rewrite -> helper7 in H. apply (IHxprog1 env0 (n * n0 :: stack)) in H.
              rewrite <- helper7 in H. assumption.
     * apply helper3 in H. assert (XMultiExec (xprog1 ++ xprog2,  n :: stack, env0) ([], empty_stack, env2)).
        { apply IHxprog1. assumption. }
        replace ((XLoadConst n :: xprog1) ++ xprog2) with (XLoadConst n :: (xprog1 ++ xprog2)).
        remember (xprog1 ++ xprog2) as xprog12.
        + apply helper3. assumption.
        + reflexivity.
    *
admit.
      (* rewrite -> helper4 in H. destruct H as [n]. destruct H. apply (IHxprog1 env0 (n :: stack)) in H.
        assert (exists n, XMultiExec (xprog1 ++ xprog2, n :: stack, env0) ([], empty_stack, env2) /\ env0 s = Some n).
        { exists n. split. assumption. assumption. } rewrite <- helper4 in H2. assumption.
      *)
   * destruct stack. 
      + apply store_cannot_be_used_with_empty_stack in H. exfalso. assumption.
        + rewrite -> helper5 in H.
          apply (IHxprog1 (s ⊢> n; env0) stack) in H.
          rewrite <- helper5 in H. assumption. 

Theorem semantic_preserved_by_seq : forall (yprog1 yprog2 : YStmt),
  semantic_preserved yprog1 ->
  semantic_preserved yprog2 ->
  semantic_preserved (YSeq yprog1 yprog2).
Proof.
  intros. unfold semantic_preserved in *.
  intros.
  unfold YisFinalStateOf in *.
  unfold XisFinalStateOf in *.
  rewrite -> prog_transl_is_concat_of_stmt_transl in H1.
  remember (compile yprog1 empty_xprog) as xprog1.
  remember (compile yprog2 []) as xprog2.
  assert (exists env1: Env, YisFinalStateOf yprog1 env0 env1).
  { apply y_finalstep_exists. }
  destruct H4 as [env0'].
  unfold YisFinalStateOf in *.
  assert (exists env0'', XisFinalStateOf xprog1 env0 env0'' empty_stack).
  { apply xexec_finalstep_exists. }
  destruct H5 as [env0''].
  unfold XisFinalStateOf in *.
  unfold empty_xprog in *.
  symmetry in Heqxprog1.
  assert (env0' = env0''). { apply (H xprog1 env0 env0' env0'' Heqxprog1 H4 H5). }
  assert (exists env1': Env, YisFinalStateOf yprog2 env0' env1').
  { apply y_finalstep_exists. }
  destruct H7 as [env1']. unfold YisFinalStateOf in *.
  assert (exists env1'', XisFinalStateOf xprog2 env0' env1'' empty_stack).
  { apply xexec_finalstep_exists. }
  destruct H8 as [env1'']. unfold XisFinalStateOf in *.
  assert (env1' = env1''). {  apply H0 with xprog2 env0'. reflexivity. assumption. assumption. }
  rewrite <- H9 in *. rewrite <- H6 in *. clear H9. clear H6. clear H. clear H0.
  clear env0''. clear env1''.
  assert (env1' = env1). {
    apply (y_sequence_is_like_piping_outputs 
              yprog1 yprog2 env0 env0' env1' env1) .
    * assumption.
    * assumption.
    * assumption. }
  assert (XMultiExec (xprog, empty_stack, env0) ([], empty_stack, env1')).
  { rewrite <- H1. apply (xprog_concat_is_like_piping_outputs xprog1 xprog2 env0 env0' env1' empty_stack).
    * assumption. * assumption. }
  assert (env1' = env2). {
  symmetry.
  apply (xexec_finalstep_is_unique xprog env0 env2 env1' empty_stack).
  * assumption.
  * assumption. }
  rewrite <- H. assumption. Qed. 

Theorem well_defined_applies_to_sub_seq_left : forall (yprog1 yprog2 : YStmt),
  well_defined (YSeq yprog1 yprog2) ->
  well_defined yprog1.
Proof. 
  intros. inversion H.
  - constructor.
  - constructor. Qed.

Theorem well_defined_applies_to_sub_seq_right : forall (yprog1 yprog2 : YStmt),
  well_defined (YSeq yprog1 yprog2) ->
  well_defined yprog2.
Proof. 
  intros. inversion H.
  - assumption.
  - assumption. Qed.

Theorem semantic_preserved_always : forall (yprog : YStmt),
  well_defined yprog ->
  semantic_preserved yprog.
Proof. 
  intros. induction yprog.
  - apply semantic_preserved_by_skip.
  - apply semantic_preserved_by_assign.
  - remember (YSeq yprog1 yprog2) as yprogSeq.
    rewrite -> HeqyprogSeq in *.
    assert (well_defined yprog1). { apply (well_defined_applies_to_sub_seq_left yprog1 yprog2 H). }
    assert (well_defined yprog2). { apply (well_defined_applies_to_sub_seq_right yprog1 yprog2 H). }
    apply (semantic_preserved_by_seq yprog1 yprog2 (IHyprog1 H0) (IHyprog2 H1)). Qed.

