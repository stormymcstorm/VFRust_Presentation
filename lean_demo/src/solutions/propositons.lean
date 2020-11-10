
-- Shows that logical and is commutative
theorem my_and_comm : ∀ p q, p ∧ q ↔ q ∧ p :=
    (
        assume p q,
        iff.intro 
        (
            assume h: p ∧ q,
            show q ∧ p, from and.intro (and.right h) (and.left h)
        ) 
        (
            assume h: q ∧ p,
            show p ∧ q, from and.intro (and.right h) (and.left h)
        )
    )

-- Show that demorgan's rules hold
theorem and_disp : ∀ p q r, p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    (
        assume p q r,
        iff.intro 
        ( -- first show LHS → RHS
            assume h : p ∧ (q ∨ r),
            have Hp : p, from and.left h,
            have Hqr : q ∨ r, from and.right h,
            or.elim Hqr
            ( -- first show p ∧ q → (p ∧ q) ∨ (p ∧ r)
                assume Hq : q,
                have Hpq : p ∧ q, from and.intro Hp Hq, 
                show (p ∧ q) ∨ (p ∧ r), from or.inl Hpq
            )
            ( -- the show p ∧ r → (p ∧ q) ∨ (p ∧ r)
                assume Hr : r,
                have Hpr : p ∧ r, from and.intro Hp Hr,
                show (p ∧ q) ∨ (p ∧ r), from or.inr Hpr
            )
        ) 
        ( -- then show RHS → LHS
            assume h : (p ∧ q) ∨ (p ∧ r),
            or.elim h 
            (
                assume Hpq : p ∧ q,
                have Hp: p, from and.left Hpq,
                have Hq: q, from and.right Hpq,
                have Hqr : q ∨ r, from or.inl Hq,
                show p ∧ (q ∨ r), from and.intro Hp Hqr
            )
            (
                assume Hpr : p ∧ r,
                have Hp : p, from and.left Hpr,
                have Hr : r, from and.right Hpr,
                have Hqr : q ∨ r, from or.inr Hr,
                show p ∧ (q ∨ r), from and.intro Hp Hqr
            )
        )
    )