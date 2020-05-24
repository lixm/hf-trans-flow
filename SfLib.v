(*
  Adapted from SfLib.v, 
  from the Software Foulndations library
  https://softwarefoundations.cis.upenn.edu/
*)

Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Import LibTactics. 
Require Export Arith.
Require Export Arith.EqNat.
Require Export Ensembles.

Require Export String.
Open Scope string_scope. 

(*Require String. Open Scope string_scope.*)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.  
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi `(X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | Multi_refl  : forall (x : X),
                 multi X R x x
  | Multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
(* Implicit Arguments multi [[X]]. *)
Arguments multi : default implicits.

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

(*
Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl. Qed.
*)

Lemma multi_back :
  forall (X : Type) (R : relation X) x y z, 
    multi R x y -> R y z -> multi R x z.
Proof.
  introv; intro H_multi.
  remember R as rel in H_multi; remember x as xx in H_multi; remember y as yy in H_multi. 
  gen x y z.
  multi_cases (induction H_multi) Case; intros; subst. 
  Case "multi_refl". eapply Multi_step; eauto; apply Multi_refl.
  Case "multi_step". specialize (IHH_multi y (eq_refl _) y0 (eq_refl _) z0 H0). 
  eapply Multi_step; eauto.
Qed.

Inductive k_R `(X:Type) (R: relation X) : nat -> X -> X -> Prop :=
| Zero_R : forall (x : X), k_R X R 0 x x 
| Suc_R : forall (x x'' x' : X) k,
    R x x'' -> k_R X R k x'' x' -> k_R X R (S k) x x'.

Tactic Notation "k_R_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "k_R_zero" | Case_aux c "k_R_inc" ].

Lemma k_back :
  forall (X : Type) (R : relation X) k x y z,
    k_R _ R k x y -> R y z -> k_R _ R (S k) x z.
Proof.
  intros.
  remember R as rel in H.
  remember k as num in H.
  remember x as xx in H.
  remember y as yy in H.
  gen k. gen x. 
  k_R_cases (induction H) Case.
  Case "k_R_zero". 
  intros. rewrite <- Heqnum.  
  econstructor; eauto.
  rewrite <- Heqxx.  rewrite Heqyy.
  eauto.
  constructor. 
  Case "k_R_inc". 
  intros.
  specialize (IHk_R Heqyy x'' (eq_refl x'') k (eq_refl k)).
  rewrite Heqrel in H.
  rewrite Heqxx in *.
  rewrite Heqnum in *.
  econstructor; eauto.
Qed.
  

(*SearchAbout "relation". *)
    
