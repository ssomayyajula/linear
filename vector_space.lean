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
  neg        := has_neg.neg,
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

instance set_is_type {α : Type u} : has_coe (set α) (Type u) :=
⟨subtype⟩

class subspace {V : Type u} [field F] [vector_space V F]
(U : set V)
--extends { vector_space (subtype U) F with add := vector_space.add }

/-def zero_scalar_mul_zero {V K} [f : field K] [s : vector_space V K] :
  ∀ v : V, f.zero ⋅ v = 0 :=
λ v, have f.zero ⋅ v =  f.zero ⋅ v + f.zero ⋅ v, from
calc f.zero ⋅ v = (f.zero + f.zero) ⋅ v   : by rw [field.add_zero _]
            ... = f.zero ⋅ v + f.zero ⋅ v : vector_space.scalar_mul_right_distrib _ _ _ _,
(calc 0 = f.zero ⋅ v - f.zero ⋅ v : (sub_self _).symm
    ... = 
    ... = f.zero ⋅ v : sorry).symm-/