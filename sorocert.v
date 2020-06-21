From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.

Inductive one_unit_beads : Type :=
| l_empty
| one
| two
| three
| four.

Inductive five_unit_beads : Type :=
| u_empty
| five.

Inductive rod : Type :=
| make_rod (f : five_unit_beads) (o : one_unit_beads).


Definition five_units (r : rod) : five_unit_beads :=
match r with
| make_rod f o => f
end.

Definition one_units (r : rod) : one_unit_beads :=
match r with
| make_rod f o => o
end.

Definition one_units_to_nat (o : one_unit_beads) : nat :=
match o with
| l_empty => 0
| one     => 1
| two     => 2
| three   => 3
| four    => 4
end.

Definition five_units_to_nat (f : five_unit_beads) : nat :=
match f with
| u_empty => 0
| five    => 5
end.

Definition rod_to_nat (r : rod) : nat :=
match r with
| make_rod f o => (five_units_to_nat f) + (one_units_to_nat o)
end.

Theorem one_units_to_nat_injective : forall o o',
one_units_to_nat o = one_units_to_nat o' -> o = o'.
Proof.
intros.
destruct o; destruct o'; try discriminate; try reflexivity.
Qed.

Theorem one_units_small : forall o,
one_units_to_nat o <= 4.
Proof.
destruct o; simpl; omega.
Qed.

Theorem five_units_to_nat_injective : forall f f',
five_units_to_nat f = five_units_to_nat f' ->
f = f'.
Proof.
intros.
destruct f; destruct f'; try discriminate; try reflexivity.
Qed.

Theorem five_units_zero_or_five : forall f,
five_units_to_nat f = 0 \/ five_units_to_nat f = 5.
Proof.
destruct f. left. reflexivity. right. reflexivity.
Qed.

Theorem five_units_one_units_decomposition : forall o f o' f',
o <= 4 ->
o' <= 4 ->
(f = 0 \/ f = 5) ->
(f' = 0 \/ f' = 5) ->
f + o = f' + o' ->
f = f' /\ o = o'.
Proof.
intros. omega.
Qed.

Theorem rod_to_nat_injective : forall r r',
rod_to_nat r = rod_to_nat r' ->
r = r'.
Proof.
intros. destruct r as [f o]. destruct r' as [f' o']. simpl in H.
assert (   five_units_to_nat f = five_units_to_nat f' 
        /\ one_units_to_nat o = one_units_to_nat o') as [HF HO].
apply five_units_one_units_decomposition; try apply one_units_small;
try apply five_units_zero_or_five. assumption.
apply one_units_to_nat_injective in HO.
apply five_units_to_nat_injective in HF. rewrite HF. rewrite HO.
reflexivity.
Qed.

Theorem rod_to_nat_surjective : forall n, exists r,
n <= 9 -> n = rod_to_nat r.
Admitted.

Definition unit_complement (o : one_unit_beads) : one_unit_beads :=
match o with
| l_empty => l_empty
| one => four
| two => three
| three => two
| four => one
end.

Theorem unit_complement_involutive : forall o,
unit_complement (unit_complement o) = o.
Proof.
destruct o; reflexivity.
Qed.

Definition five_complement (f : five_unit_beads) : five_unit_beads :=
match f with
| u_empty => five
| five => u_empty
end.

Theorem five_complement_involutive : forall f,
five_complement (five_complement f) = f.
Proof.
destruct f; reflexivity.
Qed.

Definition rod_complement (r : rod) : rod :=
match r with
| make_rod u_empty l_empty => make_rod u_empty l_empty
| make_rod five l_empty => make_rod five l_empty
| make_rod f o => make_rod (five_complement f) (unit_complement o)
end.

Theorem rod_complement_involutive : forall r,
rod_complement (rod_complement r) = r.
Proof.
(* daria para provar isso melhor usando os teoremas de involução
   mas não sei como separar os casos *)
destruct r; unfold rod_complement; destruct f; destruct o; reflexivity.
Qed.

(* just a join operation since adding and subtracting is the same *)
Definition join_five_units (f f' : five_unit_beads) : five_unit_beads :=
match f with
| u_empty => f'
| five => five_complement f'
end.

Definition succ_one_units (o : one_unit_beads) : one_unit_beads :=
match o with
| l_empty => one
| one => two
| two => three
| three => four
| four => l_empty
end.

Definition pred_one_units (o : one_unit_beads) : one_unit_beads :=
match o with
| l_empty => four
| one => l_empty
| two => one
| three => two
| four => three
end.

Definition add_one_units (o o' : one_unit_beads) : one_unit_beads :=
match o' with
| l_empty => o
| one => succ_one_units o
| two => succ_one_units (succ_one_units o)
| three => succ_one_units (succ_one_units (succ_one_units o))
| four =>
  succ_one_units (succ_one_units (succ_one_units (succ_one_units o)))
end.

Definition sub_one_units (o o' : one_unit_beads) : one_unit_beads :=
match o' with
| l_empty => o
| one => pred_one_units o
| two => pred_one_units (pred_one_units o)
| three => pred_one_units (pred_one_units (pred_one_units o))
| four =>
  pred_one_units (pred_one_units (pred_one_units (pred_one_units o)))
end.

Theorem succ_one_units_cyclic : forall o,
succ_one_units (add_one_units o four) = o.
Proof.
destruct o; reflexivity.
Qed.

Theorem pred_one_units_cyclic : forall o,
pred_one_units (sub_one_units o four) = o.
Proof.
destruct o; reflexivity.
Qed.

Definition greater_or_equal (r r' : rod) : bool :=
rod_to_nat r <=? rod_to_nat r'.

Require Import Coq.Lists.List.

Definition test_list :=
(make_rod u_empty one) :: (make_rod five two) :: nil.

Definition soroban := list rod.