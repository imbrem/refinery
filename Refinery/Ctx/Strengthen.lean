import Refinery.Ctx.SSplit

namespace Refinery

variable {α : Type u}

inductive Ctx?.Strn : Ctx? α → Ctx? α → Type _
  | nil : Strn .nil .nil
  | cons (v) : Strn Γ Δ → Strn (Γ.cons v) (Δ.cons v)
  | zero (A) : Strn Γ Δ → Strn (Γ.cons ⟨A, 0⟩) Δ
