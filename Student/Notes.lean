/-!
#10/26 Lecture
-/

def from_ab_pair_a {a b : Type} : a × b → a
| (a,_) => a

def from_ab_true_a_true {a b : Prop} : a ∧ b → a
| ⟨a,_⟩ => a

#check Sum

def sum_elim {a b y : Type} : (a ⊕ b) → (a → y) → (b → y) → y
| (Sum.inl a), f, g => f a
| (Sum.inr b), f, g => g b

#check Or.elim

theorem and_comm  {P Q : Prop} : (P ∧ Q → Q ∧ P) ∧ (Q ∧ P → P ∧ Q) :=
And.intro
  (λ ⟨p,q⟩ => ⟨q,p⟩)
  (λ ⟨q,p⟩ => ⟨p,q⟩)
