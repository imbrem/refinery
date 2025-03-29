import Refinery.Term.Extrinsic.Refinement.Wk.Relation
import Refinery.Term.Extrinsic.Wf.Basic

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α} [R.UWkCongr]

theorem Wf.rby.wk_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a.rby b)
  : (a.wk ρ).rby (b.wk ρ) := h.dwk_congr ρ

theorem Wf.eqv.wk_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a.eqv b)
  : a.wk ρ ≈ b.wk ρ := ⟨h.left.wk_congr ρ, h.right.wk_congr ρ⟩

theorem Wf.eqv.wk0_congr {Γ : Ctx? α} (x : Var? α) [hx : x.del] {A : Ty α} {a b : Wf R Γ A}
  (h : a.eqv b) : a.wk0 x ≈ b.wk0 x := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr (Γ.wk0 x) h) <;>
  simp [wk, wk0, Ctx?.Wk.ix, Ctx?.wk0, Nat.stepWk]

theorem Wf.eqv.wk1_congr {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α}
  {A : Ty α} {a b : Wf R (Γ.cons v) A} (h : a.eqv b) : a.wk1 x ≈ b.wk1 x := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr ((Γ.wk0 x).scons _) h) <;>
  simp [wk, wk1, Ctx?.Wk.ix, Ctx?.wk0, Nat.stepWk]

theorem Wf.eqv.wk2_congr {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α}
  {A : Ty α} {a b : Wf R ((Γ.cons l).cons r) A} (h : a.eqv b) : a.wk2 x ≈ b.wk2 x := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr (((Γ.wk0 x).scons _).scons _) h) <;>
  simp [wk, wk2, Ctx?.Wk.ix, Ctx?.wk0, Nat.stepWk]

theorem Wf.eqv.pwk_congr {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a.eqv b)
  : a.pwk ρ ≈ b.pwk ρ := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr ρ h) <;> simp [wk, pwk]

def Eqv.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} (a : Eqv R Δ A) : Eqv R Γ A
  := a.liftOn (λ a => e⟦a.wk ρ⟧) (λ_ _ h => sound <| Wf.eqv.wk_congr ρ h)

theorem Eqv.wk_mk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Wf R Δ A}
  : Eqv.wk ρ (e⟦a⟧) = e⟦a.wk ρ⟧ := rfl

def Eqv.wk0 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {A : Ty α} (a : Eqv R Γ A) : Eqv R (Γ.cons x) A
  := a.liftOn (λ a => e⟦a.wk0 x⟧) (λ_ _ h => sound <| Wf.eqv.wk0_congr x h)

def Eqv.wk1 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α} {A : Ty α} (a : Eqv R (Γ.cons v) A)
  : Eqv R ((Γ.cons x).cons v) A
  := a.liftOn (λ a => e⟦a.wk1 x⟧) (λ_ _ h => sound <| Wf.eqv.wk1_congr x h)

def Eqv.wk2 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α} {A : Ty α} (a : Eqv R ((Γ.cons l).cons r) A)
  : Eqv R (((Γ.cons x).cons l).cons r) A
  := a.liftOn (λ a => e⟦a.wk2 x⟧) (λ_ _ h => sound <| Wf.eqv.wk2_congr x h)

def Eqv.pwk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} (a : Eqv R Δ A) : Eqv R Γ A
  := a.liftOn (λ a => e⟦a.pwk ρ⟧) (λ_ _ h => sound <| Wf.eqv.pwk_congr ρ h)

theorem Eqv.pwk_mk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} {a : Wf R Δ A}
  : Eqv.pwk ρ (e⟦a⟧) = e⟦a.pwk ρ⟧ := rfl
