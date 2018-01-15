import .vector_space

universes u v
variable {α : Type u}

instance function_functor : functor ((→) α) :=
{ map      := λ _ _,         (∘),
  id_map   := λ _ _,         rfl,
  map_comp := λ _ _ _ _ _ _, rfl }

instance functor_has_neg {f α} [functor f] [has_neg α] : has_neg (f α) :=
⟨has_map.map has_neg.neg⟩

variable {β : Type v}

instance function_has_add [has_add β] : has_add (α → β) :=
⟨λ f g x, f x + g x⟩

def function.cst : α → β → α :=
function.const _

-- Vector space instance for functions, F ^ n, F ^ infty, etc.
instance function_vector_space [field β] : vector_space (α → β) β :=
{ add        := (+),
  -- TODO: why can't Lean infer functor_has_neg?
  neg        := @has_neg.neg _ $ @functor_has_neg ((→) α) _ _ _,
  scalar_mul := (∘) ∘ (*),
  zero       := function.cst 0,

  add_comm     := λ _ _,   funext (λ _, add_comm     _ _),
  add_assoc    := λ _ _ _, funext (λ _, add_assoc    _ _ _),
  zero_add     := λ _,     funext (λ _, zero_add     _),
  add_zero     := λ _,     funext (λ _, add_zero     _),
  add_left_neg := λ _,     funext (λ _, add_left_neg _),

  scalar_mul_assoc         := λ _ _ _, funext (λ _, mul_assoc     _ _ _),
  one_scalar_mul           := λ _,     funext (λ _, one_mul       _),
  scalar_mul_left_distrib  := λ _ _ _, funext (λ _, left_distrib  _ _ _),
  scalar_mul_right_distrib := λ _ _ _, funext (λ _, right_distrib _ _ _) }
