
-- Shows that logical and is commutative
theorem my_and_comm : ∀ p q, p ∧ q ↔ q ∧ p :=
    sorry

-- Show that demorgan's rules hold
theorem and_disp : ∀ p q r, p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    sorry