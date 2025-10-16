From Stdlib Require Import Lia ZArith.

Open Scope Z_scope.

(* DO NOT IMPORT UNICODE FROM STDLIB *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := ({x & .. {y & P} .. })
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Notation "x ∨ y" := (sum x y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (prod x y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (fun x y => prod (forall _ : x, y) (forall _ : y, x)) (at level 95, no associativity): type_scope.
Notation "¬ x" := (x -> False) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Lemma Z_bound_dec n k1 k2 : k1 <= n < k2 -> sum (n = k1) (k1+1 <= n < k2).
Proof.
  intros.
  destruct (Z.eq_dec n k1).
  - left. exact e.
  - right. lia.
Defined.

Lemma Zmod_sig {n a b} (h : n mod a = b) (hz : a ≠ 0) : {x | n = a*x+b}.
Proof.
  exists (n/a). rewrite <- h.
  exact (Z.div_mod n a hz).
Defined.

Ltac canal' k H H2:= 
  let y := eval compute in (0 <? k) in 
  tryif (constr_eq_strict true y) then
    destruct (Z_bound_dec _ _ _ H2) as [H|H];
    simpl in H; clear H2; [| rename H into H2; canal' (k-1) H H2]
  else lia.

(* canal is an abbreviation for Case ANALysis! *)
Ltac canal n k H :=
  let H2 := ident:(__H2) in
  unshelve epose proof (Z.mod_pos_bound n k _) as H2; [lia |];
  canal' (k) H H2.

Ltac canalx n k H x := 
  assert (k ≠ 0) as Hne by easy;
  canal n k H;
  destruct (Zmod_sig H Hne) as [x Hx]; clear Hne H; rename Hx into H.


