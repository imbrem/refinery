import Refinery.Term.Extrinsic.Refinement.Wk.Relation
import Refinery.Term.Extrinsic.Wf.Basic

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α} [R.UWkCongr]

def Wf.rby.wk_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a.rby b)
  : (a.wk ρ).rby (b.wk ρ) := h.dwk_congr ρ

def Wf.wk_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a ≈ b)
  : a.wk ρ ≈ b.wk ρ := ⟨h.left.wk_congr ρ, h.right.wk_congr ρ⟩

def Eqv.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} (a : Eqv R Δ A) : Eqv R Γ A
  := a.liftOn (λ a => e⟦a.wk ρ⟧) (λ_ _ h => sound <| Wf.wk_congr ρ h)
