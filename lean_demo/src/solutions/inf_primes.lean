import data.nat.prime
open nat

-- A theorem stating that there are an infinite number of primes, or
-- more precisely for any natural number N there exists a prime p ≥ N
theorem infinite_primes : ∀ N, ∃ p ≥ N, prime p := begin
    assume N : ℕ, -- take any natural number N
    
    let M := (factorial N) + 1,
    let p := min_fac M,

    -- show that p is a prime number
    have Hₚ : prime p := begin
        refine min_fac_prime _,

        have h₁ : factorial N > 0 := factorial_pos N,
        have h₂ : M > 1 := succ_lt_succ h₁,
        
        exact ne_of_gt h₂,
    end,

    use p, -- use p for ∃ p : ℕ

    split, -- split into subgoals
    
    -- show that p ≥ N
    { by_contra, -- assume p < N
        
        have h₁ : p ∣ factorial N + 1 := min_fac_dvd M,

        -- p < N ↔ p ∣ N! since N! = 1 × ⋯ × p × ⋯ N
        have h₂ : p ∣ factorial N := begin
            refine Hₚ.dvd_factorial.mpr _,

            exact le_of_not_ge h,
        end,

        have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,

        exact prime.not_dvd_one Hₚ h,
    },

    -- have already show that p is prime
    exact Hₚ,
end