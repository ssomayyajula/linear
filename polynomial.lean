import .seq

universe u

def polynomial (F : Type u) :=
sigma (seq F)

-- We define polynomials such that p(x) is definitionally sum_{i = 1}^m a_i x^i
instance polynomial_function {R : Type u} [ring R] : has_coe (polynomial R) (R → R) :=
⟨λ p x, seq.sum p.snd (λ i ai, ai * x ^ i)⟩

/-inductive has_degree {F : Type u} : polynomial F → ℕ → Prop
| z : has_degree zero 0-/
