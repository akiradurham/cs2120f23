#check Empty

-- inductive Empty : Type

inductive Chaos : Type

def from_empty (e : Empty) : Chaos := nomatch e

#check False
-- inductive False : Prop

def from_false (a : Prop) (p : False) : a := False.elim p

def from_false_true_is_false (p : False) : True = False := False.elim p

#check Unit
-- inductive PUnit : Sort u where
-- | unit : PUnit

#check True
-- inductive True : Prop where
-- | intro : True

#check True.intro

def proof_of_true : True := True.intro

-- def false_implies_true : False → True := λ f => True.intro
def false_implies_true' : False → True := λ f => False.elim f

-- structure is like inductive but for types with only one constructor
-- both introduce type defs
-- structure has default ocnstructor called mk,

#check Prod
/-
structure Prod (a : Type u) (b : Type v) where
  fst : a
  snd : b
-/

#check And
/-
structure And (a b : Prop) : Prop where
  intro :: -- takes two values
  left : a -- proof of a
  right : b -- proof of b
-/

inductive Birds_chirping : Prop
| yep
| boo

inductive Sky_blue : Prop
| yep

#check (And Birds_chirping Sky_blue)

theorem both_and : And Birds_chirping Sky_blue := And.intro Birds_chirping.boo Sky_blue.yep

namespace cs2120f23
inductive Bool : Type
| true
| false

theorem proof_equal : Birds_chirping.boo = Birds_chirping.yep := by trivial

-- In Prop all proofs are equivalent, and values are the same since they are all proofs
-- cont. Choice of values in Prop cannot influence computations

#check Sum
/-
inductive Sum (a : Type u) (b : Type v) where
  | inl (val : a) : Sum a b
  | inr (val : b) : Sum a b
-/

#check Or
/-
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

theorem one_or_other : Or Birds_chirping Sky_blue := Or.inl Birds_chirping.yep
theorem one_or_other' : Or Birds_chirping Sky_blue := Or.inr Sky_blue.yep

-- example : is like theorem but do not have to give a name

example : Or Birds_chirping (0=1) := Or.inl Birds_chirping.yep
--example : (0=1) ∨ (1=2) := _-- not a valid proposition

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
λ d =>
  match d with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q

/-
Not (no)
-/

def no (a : Type) := a → Empty

#check Not
-- Not P is to defined to be P → False

example : no Chaos := λ (c : Chaos) => nomatch c

inductive Raining : Prop

example : ¬ Raining := λ (r : Raining) => nomatch r
