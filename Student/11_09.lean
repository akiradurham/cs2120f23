/-
Predicates - A function that goes from values to propositions
  applying the predicate returns the proposition

  We say a specific parameter value satisfies a predicate if
  they yield a true proposition
  predicates specify a *parameter* that a value might have
-/

def is_even : Nat → Prop := λ n => n % 2 = 0
#reduce is_even 4

def evens : Set Nat := { n Nat | is_even n}

def pythagorean_triple : Nat → Nat → Nat → Prop
| h, x, y => h^2 = x^2 + y^2

def py_triple : Set (Nat × Nat × Nat) := { t | t.1^2 = t.2.1^2 + t.2.2^3}

#reduce py_triple (5,4,3)

def ev_len (s : String) : Prop := is_even (s.length)
#reduce ev_len "Hello!"

def ev_len_strs : Set String := { s | is_even s.length }

/-
Quanitifiers - part of the syntax of predicate logic,
allows one to assert that every object of some type of property there is at least
one object with a specified property

Universal Quantification - asserting every value *x* of type *T* satisfies
predicate *P*.
-/
- ∀ (x : T), P x
- ∃ (x : T), P x

-- Every dog is friendly
-- ∀ (d : Dog), Friendly d
-- ∀ (p q : Person), ∃ (q : Person), Loves p q
