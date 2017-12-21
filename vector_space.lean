universes u v

variables (V : Type u) (F : Type v)

class has_scalar_mul := (scalar_mul : F → V → V)

reserve infixl ` ⬝ `:70
infix ⬝ := has_scalar_mul.scalar_mul

class vector_space [f : field F] extends
  add_comm_group V, has_scalar_mul V F :=
(scalar_mul_assoc         : ∀ (a b : F) (v : V), (a * b) ⬝ v = a ⬝ (b ⬝ v))
(one_scalar_mul           : ∀ v : V,               f.one ⬝ v = v)
(scalar_mul_left_distrib  : ∀ (a : F) (u v : V), a ⬝ (u + v) = a ⬝ u + a ⬝ v)
(scalar_mul_right_distrib : ∀ (a b : F) (v : V), (a + b) ⬝ v = a ⬝ v + b ⬝ v)

/-attribute [simp] vector_space.one_scalar_mul
                 vector_space.scalar_mul_left_distrib
                 vector_space.scalar_mul_right_distrib-/

namespace function

instance {A : Type u} : functor ((→) A) :=
{ map      := λ _ _,         (∘),
  id_map   := λ _ _,         rfl,
  map_comp := λ _ _ _ _ _ _, rfl }

variables {α : Type u} {β : Type v}

-- TODO REPLACE WITH MAP DEFINITION
instance [has_add β] : has_add (α → β) := ⟨λ f g x, f x + g x⟩
instance [has_neg β] : has_neg (α → β) := ⟨λ f x, - f x⟩

end function

-- Vector space instance for functions, F ^ n, F ^ infty
instance function_vector_space {S : Type u} {F} [field F] : vector_space (S → F) F :=
{ add        := (+),
  neg        := has_neg.neg,
  scalar_mul := λ a f x, a * f x,
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

-- Convenient notation for Fⁿ
notation F `^` n := fin n → F