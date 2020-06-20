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

Definition one_unit_to_nat (o : one_unit_beads) : nat :=
match o with
| l_empty => 0
| one     => 1
| two     => 2
| three   => 3
| four    => 4
end.

Definition five_unit_to_nat (f : five_unit_beads) : nat :=
match f with
| u_empty => 0
| five    => 5
end.

Definition rod_to_nat (r : rod) :=
match r with
| make_rod f o => (five_unit_to_nat f) + (one_unit_to_nat o)
end.

Theorem one_unit_to_nat_injective : forall o o',
one_unit_to_nat o = one_unit_to_nat o' -> o = o'.
Proof.
intros.
destruct o; destruct o'; try discriminate; try reflexivity.
Qed.

Theorem one_unit_small : forall o,
one_unit_to_nat o <= 4.
Proof.
destruct o; simpl; omega.
Qed.

Theorem five_unit_to_nat_injective : forall f f',
five_unit_to_nat f = five_unit_to_nat f' ->
f = f'.
Proof.
intros.
destruct f; destruct f'; try discriminate; try reflexivity.
Qed.

Theorem five_unit_zero_or_five : forall f,
five_unit_to_nat f = 0 \/ five_unit_to_nat f = 5.
Proof.
destruct f. left. reflexivity. right. reflexivity.
Qed.

Theorem five_unit_one_unit_decomposition : forall o f o' f',
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
assert (   five_unit_to_nat f = five_unit_to_nat f' 
        /\ one_unit_to_nat o = one_unit_to_nat o') as [HF HO].
apply five_unit_one_unit_decomposition; try apply one_unit_small;
try apply five_unit_zero_or_five. assumption.
apply one_unit_to_nat_injective in HO.
apply five_unit_to_nat_injective in HF. rewrite HF. rewrite HO.
reflexivity.
Qed.