import .vector_space

open vector_space

universes u v
variables {V : Type u} {F : Type v} [field F] [vector_space V F]

class subspace (U : set V) : Prop :=
(contains_zero : (0 : V) ∈ U)
(add_closed  : ∀ {u v : V}, u ∈ U → v ∈ U → u + v ∈ U)
(mul_closed  : ∀ (a : F) {u : V}, u ∈ U → a ⋅ u ∈ U)

open subspace

instance subspace_is_vector_space {U : set V} [@subspace _ F _ _ U] : vector_space (subtype U) F :=
{ add        := λ⟨u, pu⟩ ⟨v, pv⟩, ⟨u + v, add_closed _ pu pv⟩,
  neg        := λ⟨u, pu⟩, ⟨-u, by {rw ←neg_one_scalar_mul_neg u, exact mul_closed (-1) pu}⟩,
  scalar_mul := λ a ⟨u, pu⟩, ⟨a ⋅ u, mul_closed a pu⟩,
  zero       := ⟨0, contains_zero _ _⟩,

  add_comm     := λ⟨_,_⟩ ⟨_,_⟩,       subtype.eq (add_comm _ _),
  add_assoc    := λ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩, subtype.eq (add_assoc _ _ _),
  zero_add     := λ⟨_,_⟩,             subtype.eq (zero_add _),
  add_zero     := λ⟨_,_⟩,             subtype.eq (add_zero _),
  add_left_neg := λ⟨_,_⟩,             subtype.eq (add_left_neg _),

  scalar_mul_assoc         := λ _ _ ⟨_,_⟩,       subtype.eq (scalar_mul_assoc         _ _ _),
  one_scalar_mul           := λ     ⟨_,_⟩,       subtype.eq (one_scalar_mul           _ _),
  scalar_mul_left_distrib  := λ _   ⟨_,_⟩ ⟨_,_⟩, subtype.eq (scalar_mul_left_distrib  _ _ _),
  scalar_mul_right_distrib := λ _ _ ⟨_,_⟩,       subtype.eq (scalar_mul_right_distrib _ _ _) }

-- Subset of V containing the sum of any two elements from U₁ and U₂
inductive sum_of_subsets {V F} [field F] [vector_space V F] (U₁ U₂ : set V) : set V
| intro {u v : V} : u ∈ U₁ → v ∈ U₂ → sum_of_subsets (u + v)

instance : has_add (set V) :=
⟨@sum_of_subsets _ F _ _⟩

-- Sum of subspaces is a subspace
instance sum_of_subsets_is_subspace {U₁ U₂ : set V} [@subspace _ F _ _ U₁] [@subspace _ F _ _ U₂] :
subspace (U₁ + U₂) :=
{ contains_zero := begin
    -- WTS 0 + 0 ∈ U₁ + U₂
    rw ←add_zero (0 : V),
    -- This is trivial, because 0 ∈ U₁ and 0 ∈ U₂
    split, repeat { apply contains_zero }
  end,
  add_closed := begin
    introv h1 h2,
    cases h1 with u1 u2,
    cases h2 with v1 v2,
    show (u1 + u2) + (v1 + v2) ∈ U₁ + U₂,
    -- WTS (u1 + v1) + (u2 + v2) ∈ U1 + U2
    rw [add_assoc u1 u2 (v1 + v2),
       ←add_assoc u2 v1 v2,
        add_comm  u2 v1,
        add_assoc v1 u2 v2,
       ←add_assoc u1 v1 (u2 + v2)],
    -- This is trivial since u1 + v1 ∈ U₁ and u2 + v2 ∈ U₂
    split, all_goals {apply add_closed, assumption, assumption}
  end,
  mul_closed := begin
    intros a _ h1,
    cases h1 with u v,
    show a ⋅ (u + v) ∈ U₁ + U₂, simp,
    -- WTS a ⋅ u + a ⋅ v ∈ U₁ + U₂
    -- This is trivial since a ⋅ u ∈ U₁ and a ⋅ v ∈ U₂
    split, all_goals {apply mul_closed, assumption}
  end }

-- A better-behaved singleton set
inductive just {α} (a : α) : set α
| intro : just a

instance zero_subspace : @subspace V F _ _ (just 0) :=
{ contains_zero := by split,
  add_closed := begin
    introv h1 h2,
    cases h1, cases h2,
    show (0 : V) + 0 ∈ just (0 : V),
    simp, split
  end,
  mul_closed := begin
    intros a _ h,
    cases h,
    show a ⋅ (0 : V) ∈ just (0 : V),
    simp, split
  end }

-- A vector space is the largest subspace of itself, of course
instance total_space : @subspace V F _ _ set.univ :=
{ contains_zero :=            trivial,
  add_closed    := λ _ _ _ _, trivial,
  mul_closed    := λ _ _ _,   trivial }

lemma set.empty {V} (a : V) : ¬a ∈ (∅ : set V) :=
id

lemma empty_not_subspace : ¬(@subspace V F _ _ ∅) :=
assume h : subspace ∅,
absurd h.contains_zero (set.empty 0)