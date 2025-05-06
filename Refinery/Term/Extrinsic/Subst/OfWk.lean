import Refinery.Term.Extrinsic.Subst.Effect

namespace Refinery

open HasQuant HasPQuant HasCommRel

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

def Term.Deriv?.wkOut
  {Γ : Ctx? α} {a : Term φ (Ty α)} {v w : Var? α} (ρ : v.Wk w) (D : Γ ⊢? a : v) : (Γ ⊢? a : w) :=
  match v, w, D, ρ with
  | _, _, .valid _ _ _ _, _ => sorry
  | ⟨A, 0⟩, ⟨_, 0⟩, .zero hΓ a _, _ => .zero hΓ a _


def Term.Deriv?.bv0' (Γ : Ctx? α) {v w : Var? α} (ρ : v.Wk w) :
  Γ.erase.cons v ⊢? .bv (φ := φ) 0 : w
  := (Deriv?.bv0 Γ v).wkOut ρ

def Term.SubstDS.lift' {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {v w : Var? α} (ρ : v.Wk w)
  : SubstDS φ (Γ.cons v) (Δ.cons w)
  := .cons (a := .bv 0)
           (.cons Γ.erase_right (.right _))
           (σ.wkIn (Γ.wk0 v.erase))
           sorry

def Ctx?.Wk.toSubst {Γ Δ : Ctx? α} : Γ.Wk Δ → Term.SubstDS φ Γ Δ
  | .nil => .nil inferInstance
  | .cons ρ hvw => sorry
  | .skip ρ hv => sorry

namespace Term
