import .seq

inductive is_polynomial {R} [ring R] : set (R → R)
| intro {n} (a : seq R n) : is_polynomial (λ x, seq.sum (λ i, a i * x /- ^ i -/))

def P (R) [ring R] := subtype (@is_polynomial R _)

def zero {R} [ring R] : P(R) :=
⟨λ _, 0, begin
  let a : seq R 1 := seq.const 0,
  let h : ∀ x, seq.sum (λ i, a i * x /- ^ i -/) = 0 :=
    by {intro x, show 0 * x /- ^ i -/ + 0 = 0, simp},
  rw ←funext h,
  apply is_polynomial.intro
end⟩

instance {R} [ring R] {n} : has_coe (seq R n) (P R) :=
⟨λ a, ⟨λ x, seq.sum (λ i, a i * x /- ^ i -/), is_polynomial.intro a⟩⟩

inductive with_bottom (α)
| bot : with_bottom
| intro : α → with_bottom

notation `⊥`  := with_bottom.bot _
notation `-∞` := with_bottom.bot _

instance {α} : has_coe α (with_bottom α) :=
⟨with_bottom.intro⟩

instance {α} [has_le α] : has_le (with_bottom α) :=
⟨sorry⟩

def fin.max {n} : fin (n + 1) :=
⟨n, nat.le_refl _⟩

inductive has_degree {R} [ring R] : P(R) → with_bottom ℕ → Prop
| intro_zero                    : has_degree zero -∞
| intro {n} (a : seq R (n + 1)) : a fin.max ≠ 0 → has_degree a n

def P_deg_le (n : with_bottom ℕ) (R) [r : ring R] :=
@subtype (P(R)) (λ p, ∃ m ≤ n, has_degree p m)
