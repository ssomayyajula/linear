import .seq .vector_space .subspace

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

def monoid.pow {R} [monoid R] (r : R) : ℕ → R :=
nat.rec 1 (λ _, (*) r)

notation x `^` n := monoid.pow x n

-- A function R → R is a polynomial of degree...
inductive is_polynomial_of_degree {R} [ring R] : (R → R) → with_bottom ℕ → Prop
| intro_zero :
    is_polynomial_of_degree (λ _, 0) -∞
| intro_sum {n} (a : seq R (n + 1)) :
    a fin.max ≠ 0 → is_polynomial_of_degree (λ x, seq.sum (λ i, a i * x ^ i.val)) n

def P (R) [ring R] : set (R → R) :=
λ f, ∃ n, is_polynomial_of_degree f n

def P_deg_le (n) (R) [ring R] : set (R → R) :=
λ f, ∃ m ≤ n, is_polynomial_of_degree f m

open is_polynomial_of_degree

/-def P_add_closed {R} [field R] : ∀ (u v : R → R), u ∈ P R → v ∈ P R → u + v ∈ P R
| .(function.const R 0) v ⟨-∞, .(intro_zero)⟩ _ :=
    by show 0 + v ∈ P R; simp; assumption
| _ _ _ _ := begin admit end-/

instance P_is_subspace {F} [f : field F] : @subspace (F → F) F _ _ (P F) :=
{
  contains_zero := ⟨-∞, intro_zero⟩,
  add_closed := sorry,
  mul_closed := sorry
}
/-


begin
    intros _ v h1 h2,
    cases h1 with _ h1,
    cases h1,
    
    show 0 + v ∈ P F, simp,
    assumption,
    
    cases h2 with _ h2,
    cases h2,

    --simp,
    show (λ (x : F), seq.sum (λ (i : fin (n + 1)), a_1 i * x ^ i.val)) + 0 ∈ P F,
    simp,
    assumption,
-/