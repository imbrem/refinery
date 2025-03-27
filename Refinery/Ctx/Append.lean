import Refinery.Ctx.Basic

namespace Refinery

variable {α : Type u}

def Ctx?.append (Γ Δ : Ctx? α) : Ctx? α := List.append Δ Γ

instance Ctx?.instAppend : Append (Ctx? α) := ⟨Ctx?.append⟩

@[simp]
theorem Ctx?.append_nil (Γ : Ctx? α) : Γ.append .nil = Γ := rfl

@[simp]
theorem Ctx?.nil_append (Δ : Ctx? α) : Ctx?.nil.append Δ = Δ := List.append_nil Δ

@[simp]
theorem Ctx?.append_cons (Γ Δ : Ctx? α) (v : Var? α)
  : Γ.append (Δ.cons v) = (Γ.append Δ).cons v := rfl

theorem Ctx?.append_assoc (Γ Δ Θ : Ctx? α)
  : (Γ.append Δ).append Θ = Γ.append (Δ.append Θ) := (List.append_assoc Θ Δ Γ).symm

variable [HasQuant α]

def Ctx?.Wk.append {Γ Γ' Δ Δ' : Ctx? α}
  (ρΓ : Γ'.Wk Γ) (ρΔ : Δ'.Wk Δ) : (Γ'.append Δ').Wk (Γ.append Δ)
  := match ρΓ, ρΔ with
  | ρΓ, .nil => ρΓ
  | ρΓ, .cons ρΔ hvw => (ρΓ.append ρΔ).cons hvw
  | ρΓ, .skip ρΔ hv =>  (ρΓ.append ρΔ).skip hv

@[simp]
theorem Ctx?.Wk.append_nil {Γ Γ' : Ctx? α} (ρΓ : Γ'.Wk Γ)
  : ρΓ.append .nil = ρΓ := rfl

@[simp]
theorem Ctx?.Wk.append_cons
  {Γ Γ' Δ Δ' : Ctx? α} (ρΓ : Γ'.Wk Γ) (ρΔ : Δ'.Wk Δ) {v w : Var? α} (hvw : v.Wk w)
  : ρΓ.append (ρΔ.cons hvw) = (ρΓ.append ρΔ).cons hvw := rfl

@[simp]
theorem Ctx?.Wk.append_skip
  {Γ Γ' Δ Δ' : Ctx? α} (ρΓ : Γ'.Wk Γ) (ρΔ : Δ'.Wk Δ) {v : Var? α} (hv : v.del)
  : ρΓ.append (ρΔ.skip hv) = (ρΓ.append ρΔ).skip hv := rfl

--TODO: nil_append, append_assoc, via cast
