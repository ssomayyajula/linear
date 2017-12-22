import smt.arith

def complex := real × real

notation `ℂ` := complex

-- Oh god, it's noncomputable, HELP
noncomputable def add : ℂ → ℂ → ℂ
| ⟨a, b⟩ ⟨c, d⟩ := ⟨a + c, b + d⟩

