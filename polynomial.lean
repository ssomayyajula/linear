import .seq .vector_space .subspace .function

def fin.max {n} : fin (n + 1) :=
⟨n, nat.le_refl _⟩

def monoid.pow {R} [monoid R] (r : R) : ℕ → R :=
nat.rec 1 (λ _, (*) r)

notation x `^` n := monoid.pow x n

-- A function R → R is a polynomial of degree...
inductive is_polynomial_of_degree {R} [ring R] : (R → R) → ℤ → Prop
| intro_zero :
    is_polynomial_of_degree (λ _, 0) (-1)
| intro_sum {n} (a : seq R (n + 1)) :
    a fin.max ≠ 0 → is_polynomial_of_degree (λ x, seq.sum (λ i, a i * x ^ i.val)) n

def P (R) [ring R] : set (R → R) :=
λ f, ∃ n, is_polynomial_of_degree f n

def P_deg_le (n) (R) [ring R] : set (R → R) :=
λ f, ∃ m ≤ n, is_polynomial_of_degree f m

open is_polynomial_of_degree

instance P_is_subspace {F} [f : field F] : @subspace (F → F) F _ _ (P F) :=
{ contains_zero := ⟨-1, intro_zero⟩,
  add_closed := sorry,
  mul_closed := sorry }
