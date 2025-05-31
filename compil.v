Require Import String.
Require Import List.
Require Import Arith.
Import ListNotations.
Require Import Reflect.

From Coq Require Export Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export PeanoNat.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export List.
Export ListNotations.
From Coq Require Export Permutation.

From Hammer Require Import Tactics.

(* bdestruct *)

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Definition geb (n m : nat) := m <=? n.
Hint Unfold geb : core.
Infix ">=?" := geb (at level 70) : nat_scope.

Definition gtb (n m : nat) := m <? n.
Hint Unfold gtb : core.
Infix ">?" := gtb (at level 70) : nat_scope.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.
Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Print bdestruct.

(* environnement *)

Require Import String.
From Hammer Require Import Tactics.

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

Lemma env_value_is_unique : forall (str : string) (n1 n2 : nat) (env : Env),
  env str = Some n1 ->
  env str = Some n2 ->
  n1 = n2.
Proof.
  sauto. Qed.

(* langages definitions *)

Inductive YExpr :=
    | YConst : nat -> YExpr
    | YVar : string -> YExpr
    | YAdd : YExpr -> YExpr -> YExpr
    | YMul : YExpr -> YExpr -> YExpr.

Inductive YStmt :=
    | YSkip
    | YAssign : string -> YExpr -> YStmt
    | YSeq : YStmt -> YStmt -> YStmt.

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

Inductive well_defined_expr : Env -> YExpr -> Prop :=
  | WellDef_Const : forall (env : Env) (n : nat),
    well_defined_expr env (YConst n)
  | WellDef_Var : forall (env : Env) (str : string) (n : nat),
    (env str = Some n) ->
    well_defined_expr env (YVar str)
  | WellDef_Add : forall (env : Env) (yexpr1 yexpr2 : YExpr),
    well_defined_expr env yexpr1 ->
    well_defined_expr env yexpr2 ->
    well_defined_expr env (YAdd yexpr1 yexpr2)
  | WellDef_Mul : forall (env : Env) (yexpr1 yexpr2 : YExpr),
    well_defined_expr env yexpr1 ->
    well_defined_expr env yexpr2 ->
    well_defined_expr env (YMul yexpr1 yexpr2).

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
  | YStep_Mul3 : forall (n1 n2 : nat),
    YStep_expr env (YMul (YConst n1) (YConst n2)) (YConst (n1 * n2)).

Inductive YStep : (YStmt * Env) -> (YStmt * Env) -> Prop :=
  | YStep_Assgn_reduce : forall (env : Env) (s : string) (yexpr yexpr': YExpr),
    YStep_expr env yexpr yexpr' ->
    YStep (YAssign s yexpr, env) (YAssign s yexpr', env)
  | YStep_Assgn_store : forall (env : Env) (n : nat) (s : string),
    YStep (YAssign s (YConst n), env) (YSkip, s ⊢> n ; env)
  | YStep_Seq_Skip : forall (env : Env) (yprog : YStmt),
    YStep (YSeq YSkip yprog, env) (yprog, env)
  | YStep_Seq_Assgn_reduce : 
    forall (env : Env) (yprog : YStmt) (s : string) (yexpr yexpr': YExpr),
    YStep_expr env yexpr yexpr' ->
    YStep (YSeq (YAssign s yexpr) yprog, env) (YSeq (YAssign s yexpr') yprog, env)
  | YStep_Seq_Assgn_store : forall (env : Env) (yprog : YStmt) (s : string) (n : nat),
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

Inductive YMultiStep (yprog1 : YStmt) (env1 : Env) (yprog2 : YStmt) (env2 : Env) 
  : Prop :=
  | YMultiStep_smallStep :
    YStep (yprog1, env1) (yprog2, env2) -> YMultiStep yprog1 env1 yprog2 env2
  | YMultiStep_trans : forall (yprog3: YStmt) (env3: Env),
    YMultiStep yprog1 env1 yprog3 env3 ->
    YMultiStep yprog3 env3 yprog2 env2 ->
    YMultiStep yprog1 env1 yprog2 env2.

(*
Inductive YMultiStep : (YStmt * Env) -> (YStmt * Env) -> Prop :=
  | YMultiStep_smallStep : forall (yprog1 yprog2 : YStmt) (env1 env2 : Env),
    YStep (yprog1, env1) (yprog2, env2) -> YMultiStep (yprog1, env1) (yprog2, env2)
  | YMultiStep_trans : forall (yprog1 yprog2 yprog3: YStmt) (env1 env2 env3: Env),
    YMultiStep (yprog1, env1) (yprog2, env2) ->
    YMultiStep (yprog2, env2) (yprog3, env3) ->
    YMultiStep (yprog1, env1) (yprog3, env3).
*)

Inductive XMultiExec : (XProgram * XStack * Env) -> (XProgram * XStack * Env) -> Prop :=
  | XMultiExec_smallExec : forall (xprog1 xprog2 : XProgram) (stack1 stack2 : XStack) (env1 env2 : Env),
      XExec (xprog1, stack1, env1) (xprog2, stack2, env2) -> XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2)
  | XMultiExec_trans : forall (xprog1 xprog2 xprog3: XProgram) (stack1 stack2 stack3: XStack) (env1 env2 env3: Env),
      XMultiExec (xprog1, stack1, env1) (xprog2, stack2, env2) ->
      XMultiExec (xprog2, stack2, env2) (xprog3, stack3, env3) ->
      XMultiExec (xprog1, stack1, env1) (xprog3, stack3, env3).

Definition YisFinalStateOf (yprog1 : YStmt) (env1 env2 : Env) : Prop :=
  YMultiStep yprog1 env1 YSkip env2.

Definition XisFinalStateOf (xprog1 : XProgram) (env1 env2 : Env) (stack : XStack) : Prop :=
  XMultiExec (xprog1, stack, env1) ([], [], env2).

(* well defined *)

Inductive well_defined : Env -> YStmt -> Prop  :=
  | WellDef_Skip : forall (env : Env),
      well_defined env YSkip
  | WellDef_Assign : forall (env : Env) (str : string) (yexpr : YExpr),
      well_defined_expr env yexpr ->
      well_defined env (YAssign str yexpr)
  | WellDef_Seq_Skip : forall (env : Env) (yprog : YStmt),
      well_defined env yprog ->
      well_defined env (YSeq YSkip yprog)
  | WellDef_Seq_Assign : forall (env : Env) (yprog : YStmt) (str : string) (yexpr : YExpr),
      well_defined env yprog ->
      well_defined_expr env yexpr ->
      well_defined env (YSeq (YAssign str yexpr) yprog).

(* proofs *)

Theorem expr_smallstep_possible_until_const :
  forall (env : Env) (yexpr : YExpr),
  well_defined_expr env yexpr ->
  (exists yexpr', YStep_expr env yexpr yexpr')
  \/ (exists n, yexpr = (YConst n)).
Proof.
  intros. induction yexpr.
  - right. exists n. reflexivity.
  - left. inversion H. subst. exists (YConst n).
    apply YStep_Var. assumption.
  - inversion H. subst. apply IHyexpr1 in H3. apply IHyexpr2 in H4.
    destruct H3. destruct H4.
    * destruct H0 as [yexpr1']. destruct H1 as [yexpr2'].
      left. exists (YAdd yexpr1' yexpr2).
      apply YStep_Add1. assumption.
    * destruct H0 as [yexpr1'].
      left. exists (YAdd yexpr1' yexpr2).
      apply YStep_Add1. assumption.
    * destruct H4. destruct H1 as [yexpr2'].
      left. exists (YAdd yexpr1 yexpr2'). destruct H0. rewrite -> H0.
      apply YStep_Add2. assumption.
      destruct H0. destruct H1. subst. left.
      exists (YConst (x + x0)). apply YStep_Add3.
   - sauto.
Qed.

Theorem expr_smallstep_mean_expr_multistep :
  forall (env : Env) (yexpr1 yexpr2 : YExpr),
  YStep_expr env yexpr1 yexpr2 ->
  YMultiStep_expr env yexpr1 yexpr2.
Proof. intros. apply YMultiStep_expr_smallStep. assumption. Qed.

Theorem expr_multistep_possible_until_const :
  forall (env : Env) (yexpr : YExpr),
  well_defined_expr env yexpr ->
  (exists yexpr', YMultiStep_expr env yexpr yexpr')
  \/ (exists n, yexpr = (YConst n)).
Proof.
  intros. apply expr_smallstep_possible_until_const in H.
  destruct H. destruct H as [yexpr'].
  apply expr_smallstep_mean_expr_multistep in H.
  - left. exists yexpr'. assumption.
  - right. assumption. Qed.

Theorem expr_const_dont_step : forall (n : nat) (env : Env) (yexpr : YExpr),
  YMultiStep_expr env (YConst n) yexpr -> False.
Proof.
  intros. remember (YConst n) as yconst. induction H.
  - subst. inversion H.
  - subst. apply IHYMultiStep_expr1. reflexivity.
Qed.

Theorem expr_multi_step_add_right :
  forall (env : Env) (yexpr yexpr': YExpr) (n : nat),
  YMultiStep_expr env yexpr yexpr' ->
  YMultiStep_expr env (YAdd (YConst n) yexpr) (YAdd (YConst n) yexpr').
Proof.
  intros. induction H.
  - apply YMultiStep_expr_smallStep. apply YStep_Add2. assumption.
  - apply YMultiStep_expr_trans with (YAdd (YConst n) yexpr2).
    * assumption. * assumption. Qed.

Theorem expr_multi_step_add_left :
  forall (env : Env) (yexpr yexpr' yexpr2: YExpr),
  YMultiStep_expr env yexpr yexpr' ->
  YMultiStep_expr env (YAdd yexpr yexpr2) (YAdd yexpr' yexpr2).
Proof.
  intros. induction H.
  - apply YMultiStep_expr_smallStep. apply YStep_Add1. assumption.
  - apply YMultiStep_expr_trans with (YAdd yexpr0 yexpr2).
    * assumption. * assumption. Qed.

Theorem expr_multi_step_mul_right :
  forall (env : Env) (yexpr yexpr': YExpr) (n : nat),
  YMultiStep_expr env yexpr yexpr' ->
  YMultiStep_expr env (YMul (YConst n) yexpr) (YMul (YConst n) yexpr').
Proof.
  intros. induction H.
  - apply YMultiStep_expr_smallStep. apply YStep_Mul2. assumption.
  - apply YMultiStep_expr_trans with (YMul (YConst n) yexpr2).
    * assumption. * assumption. Qed.

Theorem expr_multi_step_mul_left :
  forall (env : Env) (yexpr yexpr' yexpr2: YExpr),
  YMultiStep_expr env yexpr yexpr' ->
  YMultiStep_expr env (YMul yexpr yexpr2) (YMul yexpr' yexpr2).
Proof.
  intros. induction H.
  - apply YMultiStep_expr_smallStep. apply YStep_Mul1. assumption.
  - apply YMultiStep_expr_trans with (YMul yexpr0 yexpr2).
    * assumption. * assumption. Qed.

Theorem expr_multistep_always_reachs_end :
  forall (env : Env) (yexpr : YExpr),
  well_defined_expr env yexpr ->
  (exists n, yexpr = (YConst n))
  \/ (exists n, YMultiStep_expr env yexpr (YConst n)).
Proof.
  intros. induction yexpr.
  - left. exists n. reflexivity.
  - right. inversion H. subst. exists n. apply YMultiStep_expr_smallStep.
    apply YStep_Var. assumption.
  - inversion H. subst. apply IHyexpr1 in H3. destruct H3 as [H5 | H6].
    * destruct H5 as [n]. subst. apply IHyexpr2 in H4. destruct H4 as [H7 | H8].
      + destruct H7 as [n']. subst. right. exists (n + n').
        apply YMultiStep_expr_smallStep. apply YStep_Add3.
      + destruct H8 as [n']. right. exists (n + n').
        apply YMultiStep_expr_trans with (YAdd (YConst n) (YConst n')).
        -- apply expr_multi_step_add_right. assumption.
        -- apply YMultiStep_expr_smallStep. apply YStep_Add3.
    * destruct H6 as [n]. right. apply IHyexpr2 in H4.
      + destruct H4. destruct H1 as [n']. subst.
        -- exists (n + n').
            apply (expr_multi_step_add_left env yexpr1 (YConst n) (YConst n')) in H0.
            apply YMultiStep_expr_trans with (YAdd (YConst n) (YConst n')).
            ++ assumption.
            ++ apply YMultiStep_expr_smallStep. apply YStep_Add3.
        -- destruct H1 as [n']. exists (n + n').
            assert (YMultiStep_expr env (YAdd yexpr1 yexpr2) (YAdd (YConst n) yexpr2)).
            { apply expr_multi_step_add_left. assumption. }
            assert (YMultiStep_expr env (YAdd (YConst n) yexpr2) (YAdd (YConst n) (YConst n'))).
            { apply expr_multi_step_add_right. assumption. }
            apply YMultiStep_expr_trans with (YAdd (YConst n) yexpr2).
            ** assumption.
            ** apply YMultiStep_expr_trans with (YAdd (YConst n) (YConst n')).
                ++ assumption.
                ++ apply YMultiStep_expr_smallStep. apply YStep_Add3.
  - inversion H. subst. apply IHyexpr1 in H3. destruct H3 as [H5 | H6].
    * destruct H5 as [n]. subst. apply IHyexpr2 in H4. destruct H4 as [H7 | H8].
      + destruct H7 as [n']. subst. right. exists (n * n').
        apply YMultiStep_expr_smallStep. apply YStep_Mul3.
      + destruct H8 as [n']. right. exists (n * n').
        apply YMultiStep_expr_trans with (YMul (YConst n) (YConst n')).
        -- apply expr_multi_step_mul_right. assumption.
        -- apply YMultiStep_expr_smallStep. apply YStep_Mul3.
    * destruct H6 as [n]. right. apply IHyexpr2 in H4.
      + destruct H4. destruct H1 as [n']. subst.
        -- exists (n * n').
            apply (expr_multi_step_mul_left env yexpr1 (YConst n) (YConst n')) in H0.
            apply YMultiStep_expr_trans with (YMul (YConst n) (YConst n')).
            ++ assumption.
            ++ apply YMultiStep_expr_smallStep. apply YStep_Mul3.
        -- destruct H1 as [n']. exists (n * n').
            assert (YMultiStep_expr env (YMul yexpr1 yexpr2) (YMul (YConst n) yexpr2)).
            { apply expr_multi_step_mul_left. assumption. }
            assert (YMultiStep_expr env (YMul (YConst n) yexpr2) (YMul (YConst n) (YConst n'))).
            { apply expr_multi_step_mul_right. assumption. }
            apply YMultiStep_expr_trans with (YMul (YConst n) yexpr2).
            ** assumption.
            ** apply YMultiStep_expr_trans with (YMul (YConst n) (YConst n')).
                ++ assumption.
                ++ apply YMultiStep_expr_smallStep. apply YStep_Mul3.
Qed.

Theorem y_expr_smallstep_is_unique : forall (yexpr1 yexpr2 yexpr3 : YExpr) (env : Env),
  YStep_expr env yexpr1 yexpr2 ->
  YStep_expr env yexpr1 yexpr3 ->
  yexpr2 = yexpr3.
Proof.
  intros yexpr1 yexpr2 yexpr3 env H1 H2.
  destruct yexpr1.
  - sauto.
  - sauto.
  - generalize dependent yexpr3.
    induction H1; intros yexpr3; sauto.
  - generalize dependent yexpr3.
    induction H1; intros yexpr3; sauto.
Qed.

Fixpoint expr_length (yexpr : YExpr) : nat :=
  match yexpr with
  | YConst n => 1
  | YVar str => 2
  | YAdd yexpr1 yexpr2 => expr_length yexpr1 + expr_length yexpr2
  | YMul yexpr1 yexpr2 => expr_length yexpr1 + expr_length yexpr2
  end.

Theorem expr_smallstep_length_decreases :
  forall (env : Env) (yexpr1 yexpr2 : YExpr),
  YStep_expr env yexpr1 yexpr2 ->
  expr_length yexpr1 > expr_length yexpr2.
Proof. intros. induction H; simpl; lia. Qed.

Theorem expr_step_length_decreases :
  forall (env : Env) (yexpr1 yexpr2 : YExpr),
  YMultiStep_expr env yexpr1 yexpr2 ->
  expr_length yexpr1 > expr_length yexpr2.
Proof.
  intros. induction H.
  - apply expr_smallstep_length_decreases with env. assumption.
  - lia.
Qed.

Theorem expr_step_not_commutative :
  forall (env : Env) (yexpr1 yexpr2 : YExpr),
  YMultiStep_expr env yexpr1 yexpr2 ->
  YMultiStep_expr env yexpr2 yexpr1 ->
  False.
Proof.
  intros. assert (expr_length yexpr1 > expr_length yexpr2).
  { apply expr_step_length_decreases with env. assumption. }
  assert (expr_length yexpr2 > expr_length yexpr1).
  { apply expr_step_length_decreases with env. assumption. }
  lia.
Qed.

Theorem no_smallstep_expr_self :
  forall (env : Env) (yexpr : YExpr),
  YMultiStep_expr env yexpr yexpr -> False.
Proof.
  intros. apply expr_step_not_commutative with env yexpr yexpr.
  assumption. assumption.
Qed.

Theorem expr_smallstep_no_come_back :
 forall (env : Env) (yexpr1 yexpr2 yexpr3: YExpr),
  YMultiStep_expr env yexpr1 yexpr2 ->
  YMultiStep_expr env yexpr2 yexpr3 ->
  YMultiStep_expr env yexpr3 yexpr1 ->
  False.
Proof.
  intros. assert (YMultiStep_expr env yexpr1 yexpr3).
  { apply YMultiStep_expr_trans with yexpr2. assumption. assumption. }
  apply expr_step_not_commutative with  env yexpr1 yexpr3.
  assumption. assumption.
Qed.

Theorem smallstep_expr_is_atomic :
  forall (env : Env) (yexpr1 yexpr2 yexpr3 : YExpr),
  YStep_expr env yexpr1 yexpr3 ->
  YMultiStep_expr env yexpr1 yexpr2 ->
  YMultiStep_expr env yexpr2 yexpr3 -> False.
Proof.
  intros. generalize dependent yexpr3. induction H0.
  - intros. assert (yexpr2 = yexpr3). { apply y_expr_smallstep_is_unique with yexpr1 env. assumption. assumption. }
    subst. apply no_smallstep_expr_self in H1. assumption.
  - intros. apply IHYMultiStep_expr1 with yexpr0.
    + assumption.
    + apply YMultiStep_expr_trans with yexpr3.
      * assumption. * assumption.
Qed.

Theorem yexpr_steps_are_chained :
  forall (yexpr1 yexpr2 : YExpr) (env : Env),
  YMultiStep_expr env yexpr1 yexpr2 ->
  (forall (yexpr_chained : YExpr),
  YMultiStep_expr env yexpr1 yexpr_chained ->
    (YMultiStep_expr env yexpr2 yexpr_chained \/
    YMultiStep_expr env yexpr_chained yexpr2 \/
    yexpr_chained = yexpr2)).
Proof.
  intros. induction H.
  - generalize dependent yexpr2. induction H0.
    + intros. right. right. apply y_expr_smallstep_is_unique with yexpr1 env.
      * assumption. * assumption.
    + intros. assert (YStep_expr env yexpr1 yexpr0). { apply H. }
      apply (IHYMultiStep_expr1 yexpr0) in H.
      destruct H.
      * left. apply YMultiStep_expr_trans with yexpr2.
        -- assumption.
        -- assumption.
      * destruct H.
        -- inversion H. subst. apply (IHYMultiStep_expr2 yexpr0) in H1.
            ++ destruct H1.
                ** left. assumption.
                ** destruct H1.
                   --- right. left. assumption.
                   --- right. right. assumption.
            ++ subst. exfalso.
                apply (smallstep_expr_is_atomic env yexpr1 yexpr2 yexpr0) in H0.
                ** assumption.
                ** assumption.
                ** assumption.
        -- subst. left. assumption.
  - apply IHYMultiStep_expr1 in H0.
    destruct H0.
    + apply IHYMultiStep_expr2 in H0.
      destruct H0.
      * left. assumption.
      * destruct H0.
        -- right. left. assumption.
        -- right. right. assumption.
    + destruct H0.
      * right. left. apply YMultiStep_expr_trans with yexpr2.
        -- assumption.
        -- assumption.
      * subst. right. left. assumption.
Qed.

Theorem y_expr_finalstep_is_unique : forall (yexpr : YExpr) (env : Env) (n1 n2 : nat),
  YMultiStep_expr env yexpr (YConst n1) ->
  YMultiStep_expr env yexpr (YConst n2) ->
  n1 = n2.
Proof.
  intros.
  assert (YMultiStep_expr env yexpr (YConst n2)).
  { apply H0. }
  apply (yexpr_steps_are_chained yexpr
  (YConst n1) env H (YConst n2)) in H0.
  destruct H0.
  - apply expr_const_dont_step in H0. exfalso. assumption.
  - destruct H0.
    + apply expr_const_dont_step in H0. exfalso. assumption.
    + injection H0. intros. lia. Qed.


Theorem ysmallstep_is_unique : forall (yprog1 yprog2 yprog3 : YStmt) (env1 env2 env3 : Env),
   YStep (yprog1, env1) (yprog2, env2) ->
   YStep (yprog1, env1) (yprog3, env3) ->
   (yprog2, env2) = (yprog3, env3).
Proof. 
  intros yprog1 yprog2 yprog3 env1 env2 env3 H1 H2. induction H1.
  - inversion H2; subst.
    * assert (yexpr' = yexpr'0). 
      { apply y_expr_smallstep_is_unique with yexpr env3. assumption. assumption. }
      subst. reflexivity.
    * apply expr_smallstep_mean_expr_multistep in H.
      apply expr_const_dont_step in H. exfalso. assumption.
  - sauto.
  - sauto.
  - assert (YStep (YSeq (YAssign s yexpr) yprog, env) (YSeq (YAssign s yexpr') yprog, env)).
    { apply YStep_Seq_Assgn_reduce. assumption. }
    inversion H2; subst.
    assert (yexpr' = yexpr'0). 
    { apply y_expr_smallstep_is_unique with yexpr env3. assumption. assumption. }
     subst. reflexivity.
    apply expr_smallstep_mean_expr_multistep in H.
    apply expr_const_dont_step in H. exfalso. assumption.
  - inversion H2; subst.
    * apply expr_smallstep_mean_expr_multistep in H0.
      apply expr_const_dont_step in H0. exfalso. assumption.
    * reflexivity.
Qed.

Fixpoint yprog_length (yprog : YStmt) : nat :=
  match yprog with
  | YSkip => 1
  | YAssign str yexpr => 1 + expr_length yexpr
  | YSeq yexpr1 yexpr2 => yprog_length yexpr1 + yprog_length yexpr2
  end.

Theorem yprog_smallstep_decreases :
  forall (env1 env2 : Env) (yprog1 yprog2 : YStmt),
  YStep (yprog1, env1) (yprog2, env2) ->
  yprog_length yprog1 > yprog_length yprog2.
Proof.
  intros. induction yprog1.
  - inversion H.
  - simpl. inversion H; subst.
    * apply expr_smallstep_length_decreases in H1. 
      simpl. lia.
    * simpl. lia.
  - simpl. inversion H; subst.
    * simpl. lia.
    * simpl. apply expr_smallstep_length_decreases in H1. lia.
    * simpl. lia.
Qed.

Theorem yprog_step_decreases :
  forall (yprog1 yprog2 : YStmt) (env1 env2 : Env) ,
  YMultiStep yprog1 env1 yprog2 env2 ->
  yprog_length yprog1 > yprog_length yprog2.
Proof.
  intros. 
  induction H as 
  [yprog3 env3 yprog4 env4 H1 
  | yprog3' env3' yprog4' env4' yprog5' env5' H2 H3 H4 H5].
  - apply yprog_smallstep_decreases in H1. lia.
  - lia.
Qed.

Theorem y_step_assgn_reduce : 
  forall (env1 : Env) (yexpr yexpr': YExpr) (str : string),
  YMultiStep_expr env1 yexpr yexpr' ->
  YMultiStep (YAssign str yexpr) env1 (YAssign str yexpr') env1.
Proof.
  intros. induction H.
  - apply YMultiStep_smallStep. apply YStep_Assgn_reduce. assumption.
  - apply YMultiStep_trans with (YAssign str yexpr2) env1.
    * assumption.
    * assumption.
Qed.

Theorem step_not_commutative :
  forall (env1 env2 : Env) (yprog1 yprog2 : YStmt),
  YMultiStep yprog1 env1 yprog2 env2 ->
  YMultiStep yprog2 env2 yprog1 env1 ->
  False.
Proof.
  intros. assert (yprog_length yprog1 > yprog_length yprog2).
  { apply yprog_step_decreases with env1 env2. assumption. }
  assert (yprog_length yprog2 > yprog_length yprog1).
  { apply yprog_step_decreases with env2 env1. assumption. }
  lia.
Qed.

Theorem no_smallstep_self :
  forall (env : Env) (yprog : YStmt),
  YMultiStep yprog env yprog env -> False.
Proof.
  intros. apply step_not_commutative with env env yprog yprog.
  assumption. assumption.
Qed.

Theorem smallstep_no_come_back :
 forall (env1 env2 env3 : Env) (yprog1 yprog2 yprog3: YStmt),
  YMultiStep yprog1 env1 yprog2 env2 ->
  YMultiStep yprog2 env2 yprog3 env3 ->
  YMultiStep yprog3 env3 yprog1 env1 ->
  False.
Proof.
  intros. assert (YMultiStep yprog1 env1 yprog1 env1).
  { apply YMultiStep_trans with yprog2 env2. assumption. 
    apply YMultiStep_trans with yprog3 env3. assumption. assumption. }
  apply no_smallstep_self in H2. assumption. Qed.

Theorem smallstep_is_atomic :
  forall (env1 env2 env3 : Env) (yprog1 yprog2 yprog3 : YStmt),
  YStep (yprog1, env1) (yprog3, env3) ->
  YMultiStep yprog1 env1 yprog2 env2 ->
  YMultiStep yprog2 env2 yprog3 env3 -> False.
Proof.
  intros. generalize dependent yprog3. induction H0.
  - intros. assert ((yprog2, env2) = (yprog3, env3)).
    { apply ysmallstep_is_unique with yprog1 env1. assumption. assumption. }
    injection H2. intros. subst. apply no_smallstep_self in H1. assumption.
  - intros. apply IHYMultiStep1 with yprog0. assumption.
    apply YMultiStep_trans with yprog2 env2. assumption. assumption.
Qed.

Theorem y_steps_are_chained :
  forall (yprog1 yprog2 : YStmt) (env1 env2 : Env),
  YMultiStep yprog1 env1 yprog2 env2 ->
  (forall (yprog_chained : YStmt) (env_chained : Env),
  YMultiStep yprog1 env1 yprog_chained env_chained ->
    (YMultiStep yprog2 env2 yprog_chained env_chained \/
    YMultiStep yprog_chained env_chained yprog2 env2 \/
    ((yprog_chained = yprog2) /\ (env_chained = env2)))).
Proof.
  intros. induction H.
  - generalize dependent yprog2. induction H0.
    + intros. right. right. assert ((yprog2, env0) = (yprog0, env2)). 
      { apply ysmallstep_is_unique with yprog1 env1. assumption. assumption. }
      sauto.
    + intros. assert (YStep (yprog1, env1) (yprog0, env2)). { apply H. }
      apply (IHYMultiStep1 yprog0) in H.
      destruct H.
      * left. apply YMultiStep_trans with yprog3 env3. assumption. assumption.
      * destruct H.
        -- inversion H. apply (IHYMultiStep2 yprog0) in H1.
            ++ destruct H1.
                ** left. assumption.
                ** destruct H1.
                   --- right. left. assumption.
                   --- right. right. assumption.
            ++ subst. exfalso. 
                apply (smallstep_is_atomic env1 env4 env2 yprog1 yprog4 yprog0) in H0.
                ** assumption.
                ** sauto.
                ** assumption.
        -- sauto.
  - apply IHYMultiStep1 in H0.
    destruct H0.
    + apply IHYMultiStep2 in H0.
      destruct H0.
      * left. assumption.
      * destruct H0.
        -- right. left. assumption.
        -- right. right. assumption.
    + destruct H0.
      * right. left. sauto. 
      * sauto.
Qed.

Theorem yskip_dont_step :
  forall (yprog : YStmt) (env1 env2 : Env),
  YMultiStep YSkip env1 yprog env2 -> False.
Proof.
  intros. remember YSkip as yskip. induction H.
  - subst. inversion H.
  - subst. apply IHYMultiStep1. reflexivity.
Qed.

Theorem y_finalstep_is_unique : forall (yprog : YStmt) (env1 env2 env3 : Env),
  YMultiStep yprog env1 YSkip env2 ->
  YMultiStep yprog env1 YSkip env3 ->
  env2 = env3.
Proof. 
  intros.
  assert (YMultiStep yprog env1 YSkip env3).
  { apply H0. }
  Check y_steps_are_chained.
  apply (y_steps_are_chained yprog YSkip env1 env2
  H YSkip env3) in H0.
  destruct H0.
  - apply yskip_dont_step in H0. exfalso. assumption.
  - destruct H0.
    + apply yskip_dont_step in H0. exfalso. assumption.
    + destruct H0. sauto. Qed.

(*
Theorem helper_99 :
  forall (yexpr yexpr' : YExpr) (env1 env2 : Env) (yprog2 : YStmt) (str : string),
  YMultiStep (YSeq (YAssign str yexpr) yprog2) env1 (YSeq (YAssign str yexpr') yprog2) env2 ->
  env1 = env2.
Proof.
  Admitted.

Theorem y_step_seq_assgn_left_reduce :
  forall (env1 env3 : Env) (yexpr yexpr' : YExpr) (yprog2 yprog3 : YStmt) (str : string),
  well_defined_expr env1 yexpr ->
  YMultiStep_expr env1 yexpr yexpr' ->
  (YMultiStep (YSeq (YAssign str yexpr) yprog2) env1 yprog3 env3 <->
  YMultiStep (YSeq (YAssign str yexpr') yprog2) env1 yprog3 env3).
Proof.
  intros. split.
  - intros. assert (YMultiStep (YSeq (YAssign str yexpr) yprog2) env1
                       (YSeq (YAssign str yexpr') yprog2) env1).
    { admit. } *)
    
(*
Theorem y_step_seq_assgn_reduce : 
  forall (env env' : Env) (yexpr : YExpr) (str : string) (yprog2 : YStmt),
  YMultiStep (YAssign str yexpr) env YSkip env' ->
  YMultiStep (YSeq (YAssign str yexpr) yprog2) env yprog2 env'.
Proof.
  intros.
  assert (exists n, YMultiStep_expr env yexpr (YConst n) \/ yexpr = (YConst n)).
  { admit. }
  destruct H0 as [n]. destruct H0.
  * assert (YMultiStep (YSeq (YAssign str yexpr) yprog2) env yprog2 env'
            <-> YMultiStep (YSeq (YAssign str (YConst n)) yprog2) env yprog2 env').
    { apply y_step_seq_assgn_left_reduce. admit. assumption. }
    destruct H1. apply H2. apply YMultiStep_smallStep.
    (* show env' = env str |-> n replace and use YStep *)
    admit.
  * subst. (* show env' = env str |-> n replace and use YStep *)
    admit.

  intros. induction yexpr.
  - apply YMultiStep_smallStep. Print YStep.
    assert (YStep (YSeq (YAssign str (YConst n)) yprog2, env)
                              (yprog2, str ⊢> n; env)).
    { apply YStep_Seq_Assgn_store. }
    assert (env' = (str ⊢> n; env)). { admit. }
    subst. assumption.
  - apply YMultiStep_smallStep. Print YStep.
    (*
    assert (YStep (YSeq (YAssign str (YConst n)) yprog2, env)
                              (yprog2, str ⊢> n; env)). *) admit.
  -



  intros. induction H.
  - apply YMultiStep_smallStep. apply YStep_Assgn_reduce. assumption.
  - apply YMultiStep_trans with (YAssign str yexpr2) env1.
    * assumption.
    * assumption.
Qed. *)



Theorem y_sequence_is_like_piping_outputs :
  forall (yprog1 yprog2 : YStmt) (env1 env2 env3 : Env),
  well_defined env1 (YSeq yprog1 yprog2) ->
  YMultiStep yprog1 env1 YSkip env2 ->
  YMultiStep yprog2 env2 YSkip env3 ->
  YMultiStep (YSeq yprog1 yprog2) env1 YSkip env3.
Proof.
  intros. induction yprog1.
  - apply yskip_dont_step in H0. exfalso. assumption.
  - assert ((exists n, YMultiStep_expr env1 y (YConst n)) 
            \/ (exists n, y = (YConst n))).
    { admit. }
    destruct H2.
    *
(* 
proof sktech
first express env2 with env1 str and n, using 
YMultiStep_expr env1 y (YConst n) and YMultiStep (YAssign s y) env1 YSkip env2
to show that env2 is the result of storing y reduction in env1
second show 
YMultiStep (YSeq (YAssign s y) yprog2) env1 YSkip env3
by trans
YMultiStep (YSeq (YAssign s y) yprog2) env1 (YSeq (YAssign s (YConst n)) yprog2) env1)
-> ???
YMultiStep (YSeq (YAssign s (YConst n)) yprog2) env1 yprog2 env2 
-> applying YStep constructor by knowing env2 expression
YMultiStep yprog2 env2 YSkip env3 -> assumption

*)


(* end of the proof *)
    * destruct H2 as [n]; subst. 
      apply YMultiStep_trans with yprog2 env2.
      + assert (env2 = (s ⊢> n; env1)). { admit. } subst.
        apply YMultiStep_smallStep. apply YStep_Seq_Assgn_store.
      + assumption.
  - inversion H.



Theorem y_sequence_is_like_piping_outputs :
  forall (yprog1 yprog2 : YStmt) (env1 env2 env3 env4: Env),
  YMultiStep yprog1 env1 YSkip env2 ->
  YMultiStep yprog2 env2 YSkip env3 ->
  YMultiStep (YSeq yprog1 yprog2) env1 YSkip env4 ->
  env3 = env4.
Proof.
  intros.
  assert (YMultiStep (YSeq yprog1 yprog2) env1 YSkip env3).
  { apply helper_y1 with env2. admit. }
  apply y_finalstep_is_unique with (YSeq yprog1 yprog2) env1.
  - assumption. - assumption.
  Admitted.

Theorem remove_last_skip :
  forall (yprog1 yprog2 : YStmt) (env1 env2 : Env),
  well_defined env1 yprog1 ->
  YMultiStep yprog1 env1 yprog2 env2 ->
  YMultiStep (YSeq yprog1 YSkip) env1 yprog2 env2.
Proof.
  intros. induction yprog1.
  - apply yskip_dont_step in H0. exfalso. assumption.
  - inversion H; subst.
    apply expr_multistep_always_reachs_end in H3.
    destruct H3.
    * destruct H1 as [n]. subst. Check YStep_Seq_Assgn_store.
      assert (YMultiStep (YAssign s (YConst n)) env1 YSkip (s ⊢> n; env1)).
      + apply YMultiStep_smallStep. apply YStep_Assgn_store.
Admitted.


Theorem well_defined_remains_after_step :
  forall (yprog1 yprog2 : YStmt) (env1 env2 : Env),
  well_defined env1 (YSeq yprog1 yprog2) ->
  YMultiStep yprog1 env1 YSkip env2 ->
  well_defined env2 yprog2.
Proof. Admitted.

Theorem y_finalstep_exists : forall (yprog : YStmt) (env1 : Env),
  well_defined env1 yprog ->
  (exists env2, YisFinalStateOf yprog env1 env2)
  \/ yprog = YSkip.
Proof.
  unfold YisFinalStateOf. induction yprog; intros env1.
  - right. reflexivity.
  - left. Search well_defined_expr. inversion H; subst.
    apply expr_multistep_always_reachs_end in H2.
    destruct H2.
    * destruct H0 as [n]; subst. exists (s ⊢> n; env1).
      apply YMultiStep_smallStep. apply YStep_Assgn_store.
    * destruct H0 as [n]; subst. exists (s ⊢> n; env1).
      Check y_step_assgn_reduce.
      apply (y_step_assgn_reduce env1 y (YConst n) s) in H0.
      apply YMultiStep_trans with (YAssign s (YConst n)) env1.
      + assumption. + apply YMultiStep_smallStep. apply YStep_Assgn_store.
  - left. inversion H; subst. apply IHyprog2 in H2.
    destruct H2.
    * destruct H0 as [env2]. exists env2. apply YMultiStep_trans with yprog2 env1.
      + apply YMultiStep_smallStep. apply YStep_Seq_Skip.
      + assumption.
    * subst. exists env1. apply YMultiStep_smallStep. apply YStep_Seq_Skip.
    * inversion H; subst. 
      assert (well_defined env1 (YAssign str yexpr)).
      { apply WellDef_Assign. assumption. }
      apply IHyprog1 in H0. destruct H0.
      + destruct H0 as [env2].
        assert (well_defined env2 yprog2).
        { apply well_defined_remains_after_step with (YAssign str yexpr) env1.
          assumption. assumption. }
        apply (IHyprog2 env2) in H1. destruct H1.
        --  destruct H1 as [env4]. exists env4.
            apply YMultiStep_trans with yprog2 env2.
            ** apply no_smallstep_expr_self. assumption.
            ** assumption.
        -- subst. exists env2. apply remove_last_skip. assumption.
      + discriminate.
Qed.

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

Theorem semantic_preserved_by_skip :
  semantic_preserved YSkip.
Proof. Admitted.

Theorem skip_dont_change_env :
  forall (env1 env2 : Env),
  YMultiStep YSkip env1 YSkip env2 ->
  env1 = env2.
Proof. Admitted.

Theorem helper_y3 :
  forall (s : string) (n : nat) (env1 env2 : Env) (yprog2 : YStmt),
   YMultiStep (YAssign s (YConst n)) env1 yprog2 env2 ->
  YMultiStep YSkip (s ⊢> n; env1) yprog2 env2.
Proof.
  intros.
  apply helper_y2 with env1 (YAssign s (YConst n)).
  - apply YMultiStep_smallStep. apply YStep_Assgn_store.
  - assumption.
Qed.


Theorem helper_y5 :
  forall (yprog1 yprog2 : YStmt) (env1 env2 : Env),
  YMultiStep yprog1 env1 YSkip env2 ->
  YMultiStep (YSeq yprog1 yprog2) env1 yprog2 env2.
Proof. Abort.

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

Lemma load_execs_only_if_var_is_known :
  forall  (xprog1 : XProgram) (env1 env2 : Env) (stack1 : XStack) (s : string),
  XMultiExec (XLoadAdrs s :: xprog1, stack1, env1) ([], empty_stack, env2) ->
  exists n, (env1 s = Some n).
Proof. Admitted.

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
    *  assert (exists n, env0 s = Some n). { apply load_execs_only_if_var_is_known in H. assumption. }
        destruct H1 as [n].
        assert (XMultiExec (XLoadAdrs s :: xprog1, stack, env0) ([], empty_stack, env1) /\
       env0 s = Some n). { split. apply H. apply H1. } apply helper4 in H2.
        destruct H2.
        apply (IHxprog1 env0 (n :: stack)) in H2.
        assert (XMultiExec (xprog1 ++ xprog2, n :: stack, env0) ([], empty_stack, env2) /\ env0 s = Some n).
        { split. apply H2. apply H3. } rewrite <- helper4 in H4. destruct H4. assumption.
   * destruct stack.
      + apply store_cannot_be_used_with_empty_stack in H. exfalso. assumption.
        + rewrite -> helper5 in H.
          apply (IHxprog1 (s ⊢> n; env0) stack) in H.
          rewrite <- helper5 in H. assumption. Qed.

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
  { admit. (* apply y_finalstep_exists. *) }
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
  { admit. (* apply y_finalstep_exists. *) }
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
  rewrite <- H. assumption.
  Admitted.

Theorem well_defined_applies_to_sub_seq_left : 
  forall (yprog1 yprog2 : YStmt) (env : Env),
  well_defined env (YSeq yprog1 yprog2) ->
  well_defined env yprog1.
Proof.
  intros. inversion H.
  - constructor.
  - constructor.
  Admitted.

Theorem well_defined_applies_to_sub_seq_right : 
  forall (yprog1 yprog2 : YStmt) (env : Env),
  well_defined env (YSeq yprog1 yprog2) ->
  well_defined env yprog2.
Proof.
  intros. inversion H.
  - assumption.
  - assumption. Qed.

Theorem semantic_preserved_always : forall (yprog : YStmt) (env : Env),
  well_defined env yprog ->
  semantic_preserved yprog.
Proof.
  intros. induction yprog.
  - apply semantic_preserved_by_skip.
  - apply semantic_preserved_by_assign.
  - remember (YSeq yprog1 yprog2) as yprogSeq.
    rewrite -> HeqyprogSeq in *.
    assert (well_defined env yprog1). { apply (well_defined_applies_to_sub_seq_left yprog1 yprog2 env H). }
    assert (well_defined env yprog2). { apply (well_defined_applies_to_sub_seq_right yprog1 yprog2 env H). }
    apply (semantic_preserved_by_seq yprog1 yprog2 (IHyprog1 H0) (IHyprog2 H1)). Qed.
