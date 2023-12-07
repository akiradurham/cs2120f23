import Mathlib.Data.Set.Basic

/-!
# Final Exam: Part 2

Here you can show that you've got what we covered in class,
up to and including set theory. The focus is on set theory,
as it encompassess the underlying logic as well. A hint: You
will want to review the existential quantifier and proofs of
existentially quantified propositions.

## Problem #1:

Use set comprehension notation in Lean to define *odds*
as the set of odd numbers, by way of a membership predicate
for this set.
-/

-- Here
def odd : Nat → Prop := λ n => n % 2 = 1
def odds: Set Nat := { n | odd n }

#reduce odds 1
#reduce odds 2
#reduce odds 68
#reduce odds 67

/-!
## Problem #2:

Use set comprehension and other set notations in Lean to
define the set, *perfect_squares*, of natural numbers, n,
such that each n is the square of some natural number, m.
For example, 36 is a perfect square because it is the square
of another number, namely m = 6.
-/

-- Here

This part here

-- def square (n : Nat) : Prop := ∃ (m : Nat), n = m * m
-- def perfect_squares : Set Nat := { n | square n}

def perfect_squares : Set Nat := { n | ∃ m : ℕ, n = m^2 }


#reduce perfect_squares 6
#reduce perfect_squares 4

/-!
## Problem #3:

Use set comprehension notation to define the set, odd_perfects,
to be the intersection of the odds and the perfect squares.
-/

-- Here
def odd_perfects := perfect_squares ∩ odds

#reduce odd_perfects 37
#reduce odd_perfects 16
#reduce odd_perfects 25

/-!
## Problem #4:

Formally state and prove the proposition that 9 ∈ odd_perfects.
Hint: A proof within a proof.
-/

-- Here
example : 9 ∈ odd_perfects := ⟨ ⟨ 3, rfl ⟩ , rfl ⟩
