import data.stream
import data.vector

-- /Sequences/ of length n with elements in α
def seq (α) (n) :=
fin n → α

-- Streams (infinite sequences) are a subtype of finite ones (spooky)
/-instance {α : Type u} {n} : has_coe (stream α) (seq α n) :=
⟨λ f, f ∘ fin.val⟩-/

-- Convenient notation for Fⁿ
notation F `^` n := seq F n
notation F `∞`   := stream F

namespace seq

def const {α} {n} : α → seq α n :=
function.const _

def empty {α} : seq α 0 :=
fin.elim0

-- TODO: copy vector notation
universe u
instance {α : Type u} : has_emptyc (seq α 0) :=
⟨empty⟩

inductive mem {α n} (a : seq α n) : set α
| intro (i : fin n) : mem (a i)

instance {α : Type u} {n} : has_mem α (seq α n) :=
⟨flip mem⟩

def cons {α n} (e : α) (a : seq α n) : seq α (n + 1)
| ⟨0,     _⟩ := e
| ⟨i + 1, h⟩ := a ⟨i, nat.le_of_succ_le_succ h⟩

def snoc {α n} (a : seq α n) (e : α) : seq α (n + 1)
| ⟨i, h⟩ := if h' : i = n then e else a ⟨i, lt_of_le_of_ne (nat.le_of_succ_le_succ h) h'⟩

-- Iterates through a sequence backwards using an accumulation function
def iterate {α β n} (a : seq α n) (b : β) (f : fin n → α → β → β) : β :=
@nat.rec (λ i, i ≤ n → β)
  -- Return the default value on n = 0
  (λ _, b)
  -- Iterate on the initial j = i - 1 subsequence, and then apply f on a i
  (λ j r h,
    let i : fin n := ⟨j, h⟩ in
    f i (a i) $ r $ le_of_lt h)
n (le_refl n)

-- Summation of a sequence with elements in an additive monoid
def sum {α n} [add_monoid α] (a : seq α n) : α :=
a.iterate 0 (λ _, (+))

instance vector_to_seq {α n} : has_coe (vector α n) (seq α n) :=
⟨vector.nth⟩

instance seq_to_vector {α n} : has_coe (seq α n) (vector α n) :=
⟨vector.of_fn⟩

end seq
