import .vector_space .seq

universes u v
variables {V : Type u} {F : Type v} [f : field F] [vsi : @vector_space V F f]

-- Linear span of a finite list/seq of vectors
inductive span : ∀ {n}, seq V n → set V
-- span(∅) = {0}
| intro_empty : span seq.empty vsi.zero
-- span(v_1,...,v_n) = {sum a_iv_i | a_i ∈ F}
| intro_combo {n} (vs : seq V (n + 1)) :
    ∀ as : seq F (n + 1), span vs $ seq.sum (λ i, as i ⋅ vs i)