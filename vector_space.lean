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
  ... = v' + (v + -v) : by rw ←add_right_neg _
  ... = (v' + v) + -v : (add_assoc _ _ _).symm
  ... = (v + v') + -v : by rw add_comm v v'
  ... = 0 + -v        : by rw h
  ... = -v            : zero_add _⟩

lemma neg_one_scalar_mul_neg {V F} [f : field F] [vector_space V F] :
  ∀ (v : V), -f.one ⋅ v = -v := sorry

lemma zero_scalar_mul_zero {V F} [f : field F] [vector_space V F] :
  ∀ (v : V), f.zero ⋅ v = 0 := sorry

lemma scalar_mul_zero_zero {V F} [f : field F] [vs : vector_space V F] :
  ∀ (a : F), a ⋅ vs.zero = 0 := sorry

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
