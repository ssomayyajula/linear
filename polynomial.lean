import .seq

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

-- A function R → R is a polynomial of degree...
inductive is_polynomial_of_degree {R} [ring R] : (R → R) → with_bottom ℕ → Prop
| intro_zero :
    is_polynomial_of_degree (λ _, 0) -∞
| intro_sum {n} (a : seq R (n + 1)) :
    a fin.max ≠ 0 → is_polynomial_of_degree (λ x, seq.sum (λ i, a i * x /- ^ i -/)) n

def P (R) [ring R] : set (R → R) :=
λ f, ∃ n, is_polynomial_of_degree f n

def P_deg_le (n) (R) [ring R] : set (R → R) :=
λ f, ∃ m ≤ n, is_polynomial_of_degree f m

