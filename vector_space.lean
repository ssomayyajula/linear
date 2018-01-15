universes u v

section
variables (V : Type u) (F : inout Type v)

class has_scalar_mul :=
(scalar_mul : F → V → V)

reserve infixl ` ⋅ `:70
infix ⋅ := has_scalar_mul.scalar_mul

class vector_space [field F] extends add_comm_group V, has_scalar_mul V F :=
(scalar_mul_assoc         : ∀ (a b : F) (v : V), (a * b) ⋅ v = a ⋅ (b ⋅ v))
(one_scalar_mul           : ∀ v : V,             (1 : F) ⋅ v = v)
(scalar_mul_left_distrib  : ∀ (a : F) (u v : V), a ⋅ (u + v) = a ⋅ u + a ⋅ v)
(scalar_mul_right_distrib : ∀ (a b : F) (v : V), (a + b) ⋅ v = a ⋅ v + b ⋅ v)
end

open vector_space

attribute [simp]
one_scalar_mul scalar_mul_left_distrib scalar_mul_right_distrib

variables {V : Type u} {F : Type v} [field F] [vector_space V F]

@[simp] lemma zero_scalar_mul_zero (v : V) : (0 : F) ⋅ v = 0 :=
have (0 : F) ⋅ v + (0 : F) ⋅ v = (0 : F) ⋅ v + 0,
  by rw ←scalar_mul_right_distrib; simp,
add_left_cancel this

@[simp] lemma scalar_mul_zero_zero (a : F) : a ⋅ (0 : V) = 0 :=
have a ⋅ 0 + a ⋅ 0 = a ⋅ (0 : V) + 0,
  by rw ←scalar_mul_left_distrib; simp,
add_left_cancel this

@[simp] lemma neg_one_scalar_mul_neg (v : V) : (-1 : F) ⋅ v = -v :=
have (-1 : F) ⋅ v + v = 0, from calc
(-1 : F) ⋅ v + v = (-1 : F) ⋅ v + (1 : F) ⋅ v : by simp
             ... = (-1 + 1 : F) ⋅ v           : by rw ←scalar_mul_right_distrib
             ... = 0                          : by simp,
eq_neg_of_add_eq_zero this

lemma neg_scalar_mul_neg (a : F) (v : V) : -a ⋅ v = -(a ⋅ v) :=
by rw [neg_eq_neg_one_mul, scalar_mul_assoc]; simp
