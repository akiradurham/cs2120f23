example : ¬ False := λ f => False.elim f

example (P : Prop) : ¬ (P ∧ ¬P) := λ pandnp => (pandnp.right) (pandnp.left)
example (P : Prop) : ¬ (P ∧ ¬P) := λ pandnp => nomatch pandnp
example (P : Prop) : ¬ (P ∧ ¬P) := λ ⟨ p,np ⟩  => np p

-- equivalent to =>  (P ∧ ¬P) → False
-- proof of not p is a function that gives a proof of false, proof of no proofs / uninhabited

example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
fun pq qr p => qr (pq p)

example (a b y : Type) : (a → b) → (b → y) → (a → y) :=
fun ab bc => fun a => bc (ab a)

example (P Q R : Prop) : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
| Or.inl p => ⟨ Or.inl p, Or.inl p ⟩
| Or.inr ⟨ q, r ⟩ => ⟨ Or.inr q, Or.inr r ⟩

/-
Law of the Excluded Middle - The below is always true, since we cannot argue either side
-/
axiom em : ∀ (P : Prop), P ∨ ¬P

example : X ∨ ¬X := em X

example (A B : Prop) : ¬(A ∧ B) → ¬A ∨ ¬B
| nab => Or.inl

example (A B : Prop) : ¬A ∨ ¬B → ¬(A ∧ B)
| Or.inl na => λ ⟨ a, _ ⟩ => na a
| Or.inr nb => λ ⟨ _, b ⟩ => nb b
