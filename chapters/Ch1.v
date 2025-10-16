From Stdlib Require Import Lia ZArith.
From DiscreteMath12 Require Import Extra.

(* Here, ∃ is a notation for 'sigT'. *)
Notation "( x | y )" := (∃z, y = z*x) (at level 0).

(* Dars 2 *)

(* Page 16 (Exercises) *)

Lemma Ex1_l1 : ∀ a b c d, (a*b = c*d) → (a | c*d).
Proof.
    intros.
    exists b.
    lia.
Defined.

Local Lemma little_lemma : 6*2=3*4. easy. Defined.

Compute projT1 (Ex1_l1 6 2 3 4 little_lemma).

Lemma Ex1_l2 : ∀ a b c d, (a*b = c*d) → (b | c*d).
Proof.
    intros. exists a. lia.
Defined.

Lemma Ex1_l3 a b c d : (a*b = c*d) → (c | a*b).
Proof.
    intros. exists d. lia.
Defined.

Lemma Ex1_l4 a b c d (H : a*b = c*d) : (d | a*b).
Proof.
    intros. exists c. lia.
Defined.

Lemma Ex1_l5 a b c d (H : a*b = c*d) : (a*b | c*d).
Proof.
    exists 1. lia.
Defined.

Theorem Ex1 a b c d : (a*b = c*d) → 
    (a | c*d) ∧ (b | c*d) ∧
    (c | a*b) ∧ (d | a*b) ∧  
    (a*b | c*d).
Proof.
    intros.
    repeat (split).
    - apply (Ex1_l1 a b c d H).
    - apply (Ex1_l2 a b c d H).
    - apply (Ex1_l3 a b c d H).
    - exists c. lia.
    - exists 1. lia.
Defined.

Compute projT1 (fst (Ex1 6 32 32 6 (Z.mul_comm 6 32))).

Lemma Ex2_l1 a b : (a | b) -> (a | -b).
Proof.
    intros.
    destruct H.
    exists (-x).
    lia.
Defined.

Lemma Ex2_l2 a b : (a | b) -> (-a | b).
Proof.
    intros.
    destruct H.
    exists (-x).
    lia.
Defined.

Lemma Ex2_l3 a b : (a | b) -> (-a | -b).
Proof.
    intros.
    destruct H.
    exists x.
    lia.
Defined.

Theorem Ex2 a b : (a | b) ->  (a | -b) ∧ (-a | b) ∧ (-a | -b).
Proof.
    intros.
    repeat (split).
    - apply (Ex2_l1 a b H).
    - apply (Ex2_l2 a b H).
    - apply (Ex2_l3 a b H).
Defined.

Lemma property_1 a b m : (a | b) -> (a | m*b).
Proof.
    intros.
    destruct H.
    exists (m*x).
    lia.
Defined.

Lemma property_2 a b c : (a | b) ∧ (b | c) -> (a | c).
Proof.
    intros.
    destruct H as [Hab Hbc].
    destruct Hab as [x Hab].
    destruct Hbc as [y Hbc].
    exists (x*y).
    lia.
Defined.

Lemma property_3 a b c : (a | b) ∧ (a | c) -> (a | b + c).
Proof.
    intros.
    destruct H as [Hab Hac].
    destruct Hab as [x Hab].
    destruct Hac as [y Hac].
    exists (x+y).
    lia.
Defined.

Import Znumtheory.

Theorem Ex3 a k : (1 < a) → (a | 9*k+4)
     → (a | 5*k+3) → prime a.
Proof.
    intros.

    Search "induction" Z.
    Print prime'.
    Search prime.
Defined.

