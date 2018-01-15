import .vector_space .seq .subspace

universes u v
variables {V : Type u} {F : Type v} [field F] [vector_space V F]

-- Linear span of a finite list/seq of vectors
inductive span {n} (v : seq V n) : set V
-- span(v_1,...,v_n) = {sum a_iv_i | a_i ∈ F}
| intro (a : seq F n) : span (seq.sum (λ i, a i ⋅ v i))

theorem set.ext {α} {s₁ s₂ : set α} : (∀ a : α, a ∈ s₁ ↔ a ∈ s₂) ↔ s₁ = s₂ :=
⟨λ h, funext (λ a, propext (h a)), λ p _, by rw p⟩

-- span(∅) = {0}
lemma span_empty : @span _ F _ _ 0 ∅ = just (0 : V) :=
begin
  -- Show v ∈ span ∅ ↔ v ∈ {0}
  apply set.ext.mp, intro,
  apply iff.intro,
  -- Trivial, sum always evaluates to 0
  all_goals {intro h, cases h, split},
  exact seq.empty,
end

lemma sum_zero {n} {v : seq V n} : seq.sum (λ i, (0 : F) ⋅ v i) = (0 : V) :=
begin
  induction n with m ih,
  refl,
  --show seq.iterate (λ i, (0 : F) ⋅ v i) 0 (λ _, (+)) = 0,
  simp * at *,
  --rw ih,
  --show (0 : V) + seq.sum (λ (i : fin (nat.succ m)), 0) = 0
  admit
end

--variables {m : ℕ} {v : seq V (m + 1)}
--#check (0 : V) + seq.sum (λ (i : fin (nat.succ m)), 0) = 0

instance span_is_subspace {n} {vs : seq V n} :
  @subspace _ F _ _ (@span _ F _ _ _ vs) :=
{ contains_zero := by rw ←sum_zero; split,
  add_closed    := sorry,
  mul_closed    := sorry }

def linearly_independent {n} (v : seq V n) :=
∀ a : seq F n, seq.sum (λ i, a i ⋅ v i) = 0 → a = 0

/-def is_basis {n} (v : seq V n) :=
  (linearly_independent v) ∧ ((@span V F f vsi n v) = (@set.univ V))-/