universes u v

variables (V : Type u) (F : Type v)

class has_scalar_mul :=
(scalar_mul : F → V → V)

reserve infixl ` ⋅ `:70
infix ⋅ := has_scalar_mul.scalar_mul

class vector_space [f : field F] extends
  add_comm_group V, has_scalar_mul V F :=
(scalar_mul_assoc         : ∀ (a b : F) (v : V), (a * b) ⋅ v = a ⋅ (b ⋅ v))
(one_scalar_mul           : ∀ v : V,               f.one ⋅ v = v)
(scalar_mul_left_distrib  : ∀ (a : F) (u v : V), a ⋅ (u + v) = a ⋅ u + a ⋅ v)
(scalar_mul_right_distrib : ∀ (a b : F) (v : V), (a + b) ⋅ v = a ⋅ v + b ⋅ v)

open vector_space


lemma add_inv_unique {G} [add_comm_group G] :
  ∀ (a : G), ∃! (a' : G), a + a' = 0 :=
λ v, ⟨-v, add_right_neg v, λ v' h, calc
   v' = v' + 0        : (add_zero _).symm
  ... = v' + (v + -v) : congr_arg _ (add_right_neg _).symm
  ... = (v' + v) + -v : (add_assoc _ _ _).symm
  ... = (v + v') + -v : congr_arg (λ x, x + -v) (add_comm _ _)
  ... = 0 + -v        : congr_arg (λ x, x + -v) h
  ... = -v            : zero_add _⟩

/-lemma neg_one_scalar_mul_neg {V F} [field F] [vector_space V F] :
  ∀ (v : V), ( field.one) ⋅ v = -v := sorry-/

/-attribute [simp] vector_space.one_scalar_mul
                 vector_space.scalar_mul_left_distrib
                 vector_space.scalar_mul_right_distrib-/

instance function_functor {A : Type u} : functor ((→) A) :=
{ map      := λ _ _,         (∘),
  id_map   := λ _ _,         rfl,
  map_comp := λ _ _ _ _ _ _, rfl }

-- TODO GENERALIZE
instance function_has_add {α : Type u} {β} [has_add β] : has_add (α → β) :=
⟨λ f g x, f x + g x⟩

instance functor_has_neg {f α} [functor f] [has_neg α] : has_neg (f α) :=
⟨has_map.map has_neg.neg⟩

-- Vector space instance for functions, F ^ n, F ^ infty, polynomials
instance function_vector_space {S : Type u} {F} [field F] : vector_space (S → F) F :=
{ add        := (+),
  -- TODO: why can't Lean infer functor_has_neg?
  neg        := @has_neg.neg _ $ @functor_has_neg ((→) S) _ _ _,
  scalar_mul := (∘) ∘ (*),
  zero       := function.const _ 0,

  add_comm     := λ _ _,   funext (λ _, add_comm     _ _),
  add_assoc    := λ _ _ _, funext (λ _, add_assoc    _ _ _),
  zero_add     := λ _,     funext (λ _, zero_add     _),
  add_zero     := λ _,     funext (λ _, add_zero     _),
  add_left_neg := λ _,     funext (λ _, add_left_neg _),

  scalar_mul_assoc         := λ _ _ _, funext (λ _, mul_assoc     _ _ _),
  one_scalar_mul           := λ _,     funext (λ _, one_mul       _),
  scalar_mul_left_distrib  := λ _ _ _, funext (λ _, left_distrib  _ _ _),
  scalar_mul_right_distrib := λ _ _ _, funext (λ _, right_distrib _ _ _) }

-- TODO: is this the only way to lift subsets to types?
instance set_is_type {α : Type u} : has_coe (set α) (Type u) :=
⟨subtype⟩

class subspace {V F} [field F] [s : vector_space V F] (U : set V) :=
(zero_closed : s.zero ∈ U)
(add_closed  : ∀ {u v : V}, u ∈ U → v ∈ U → u + v ∈ U)
(mul_closed  : ∀ (a : F) {u : V}, u ∈ U → a ⋅ u ∈ U)

open subspace

instance subspace_is_vector_space {V F} [field F] [vector_space V F] (U : set V) [@subspace V F _ _ U] : vector_space (subtype U) F :=
{ add        := λ u v, ⟨u.val + v.val, add_closed _ u.property v.property⟩,
  neg        := λ u, ⟨-u.val, sorry⟩, -- TODO: Use fact that -1 * v = -v
  scalar_mul := λ a u, ⟨a ⋅ u.val, mul_closed _ u.property⟩,
  zero       := ⟨0, zero_closed _ _⟩,

  add_comm     := λ _ _,   subtype.eq (add_comm _ _),
  add_assoc    := λ _ _ _, subtype.eq (add_assoc _ _ _),
  zero_add     := λ _,     subtype.eq (zero_add _),
  add_zero     := λ _,     subtype.eq (add_zero _),
  add_left_neg := λ _,     subtype.eq (add_left_neg _),

  scalar_mul_assoc         := λ _ _ _, subtype.eq (scalar_mul_assoc         _ _ _),
  one_scalar_mul           := λ _,     subtype.eq (one_scalar_mul           _ _),
  scalar_mul_left_distrib  := λ _ _ _, subtype.eq (scalar_mul_left_distrib  _ _ _),
  scalar_mul_right_distrib := λ _ _ _, subtype.eq (scalar_mul_right_distrib _ _ _) }

-- Subset of V containing the sum of any elements from U₁ and U₂
inductive sum_of_subsets {V F} [field F] [vector_space V F] (U₁ U₂ : set V) : set V
| intro {u v : V} : u ∈ U₁ → v ∈ U₂ → sum_of_subsets (u + v)

-- Span of a set
/-inductive span {V F} [field F] [vector_space V F] (U : set V) : set V
| intro {n} : ∀ (vs : seq (subtype U) n) (as : seq F n), span (seq.sum vs (λ i vi, sorry))-/

-- Sum of subsets is a subspace
instance sum_of_subsets_is_subspace {V F} [field F] [vector_space V F] {U₁ U₂ : set V} [@subspace _ F _ _ U₁] [@subspace _ F _ _ U₂] :
@subspace _ F _ _ (@sum_of_subsets _ F _ _ U₁ U₂) :=
{ zero_closed := begin
    rw (add_zero (add_comm_group.zero V)).symm,
    apply sum_of_subsets.intro,
    repeat {apply zero_closed}
  end,
  add_closed := begin
    intros _ _ h1 h2,
    cases h1 with u1 u2,
    cases h2 with v1 v2,
    show (u1 + u2) + (v1 + v2) ∈ sum_of_subsets U₁ U₂,
    -- WTS (u1 + v1) + (u2 + v2) in U1 + U2
    rw [add_assoc u1 u2 (v1 + v2),
       ←add_assoc u2 v1 v2,
        add_comm  u2 v1,
        add_assoc v1 u2 v2,
       ←add_assoc u1 v1 (u2 + v2)],
    apply sum_of_subsets.intro,
    repeat {apply add_closed, assumption, assumption}
  end,
  mul_closed := begin
    intros a _ h1,
    cases h1 with u v,
    show a ⋅ (u + v) ∈ sum_of_subsets U₁ U₂,
    rw (scalar_mul_left_distrib a u v),
    apply sum_of_subsets.intro,
    repeat {apply mul_closed, assumption}
  end }

-- Therefore, it is also a vector space!

/-lemma small {V F} [field F] [vector_space V F] (U₁ U₂ : set V) :
  ∀ (U₃ : set V), U₁ ⊆ U₃ → U₂ ⊆ U₃ → (@sum_of_subsets _ F _ _ U₁ U₂) ⊆ U₃ :=
sorry-/

/-def zero_scalar_mul_zero {V K} [f : field K] [s : vector_space V K] :
  ∀ v : V, f.zero ⋅ v = 0 :=
λ v, have f.zero ⋅ v =  f.zero ⋅ v + f.zero ⋅ v, from
calc f.zero ⋅ v = (f.zero + f.zero) ⋅ v   : by rw [field.add_zero _]
            ... = f.zero ⋅ v + f.zero ⋅ v : vector_space.scalar_mul_right_distrib _ _ _ _,
(calc 0 = f.zero ⋅ v - f.zero ⋅ v : (sub_self _).symm
    ... = 
    ... = f.zero ⋅ v : sorry).symm-/

def setext {α} (s₁ s₂ : set α) : (∀ a : α, a ∈ s₁ ↔ a ∈ s₂) ↔ s₁ = s₂ :=
begin
  apply iff.intro,
  
  intro h,
  apply funext,
  intro x,
  apply propext,
  exact h x,

  intro h,
  rw h,
  intro,
  refl
end
