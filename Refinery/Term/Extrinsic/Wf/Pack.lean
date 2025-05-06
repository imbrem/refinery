import Refinery.Term.Extrinsic.Wf.Wk
import Refinery.Ctx.Append

open HasQuant HasPQuant HasCommRel

namespace Refinery

variable {φ : Type u} {α : Type v}

def Ctx?.rety (Γ : Ctx? α) : Ty α
  := match Γ with
  | .nil => .unit
  | .cons Γ v => v.ety.tensor Γ.rety

namespace Term

variable {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

def Wf.ebv0 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} : Wf R (Γ.cons v) v.ety := match v with
  | ⟨_, 0⟩ => .unit _
  | ⟨_, (_ : Quant)⟩ => .bv0

def Wf.pack : (Γ : Ctx? α) → Wf R Γ Γ.ety
  | .nil => .unit .nil
  | .cons Γ v => .pair Γ.erase_right.right ((pack Γ).wk0 v.erase) .ebv0

def Eqv.ebv0 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} : Eqv R (Γ.cons v) v.ety := match v with
  | ⟨_, 0⟩ => .unit _
  | ⟨_, (_ : Quant)⟩ => .bv0

theorem Eqv.ebv0_eq {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α}
  : Eqv.ebv0 (R := R) (Γ := Γ) (v := v) = e⟦Wf.ebv0⟧ := by
  cases v using Var?.casesZero <;> rfl

variable [R.UWkCongr]

def Eqv.pack : (Γ : Ctx? α) → Eqv R Γ Γ.ety
  | .nil => .unit .nil
  | .cons Γ v => .pair Γ.erase_right.right ((pack Γ).wk0 v.erase) .ebv0

theorem Eqv.pack_eq {Γ : Ctx? α} : Eqv.pack (R := R) (Γ := Γ) = e⟦Wf.pack Γ⟧ := by
  induction Γ <;> simp [Eqv.pack, Wf.pack, ebv0_eq, *] <;> rfl

def Eqv.bvAppend (Γ Δ : Ctx? α) [hΓ : Γ.del] [hΔ : Δ.del] {A : Ty α} {q : Quant}
  : Eqv R (Γ.cons ⟨A, q⟩ ++ Δ) A := Eqv.bv Δ.length (Γ.atAppend Δ _ _ (by simp))

def Eqv.wkAppend {Γ Δ : Ctx? α} (a : Eqv R (Γ ++ Δ) A) (v : Var? α) [hv : v.del]
  : Eqv R (Γ.cons v ++ Δ) A := a.wk (Γ.wkAppend Δ v)

def Eqv.swapAppendQ {Γ Δ : Ctx? α} {q : Quant} (a : Eqv R ((Γ ++ Δ).cons ⟨A, q⟩) B)
  : Eqv R (Γ.cons ⟨A, q⟩ ++ Δ) B
  := .let₁ (Γ.erase_right.right.append Δ.erase_right)
      (bvAppend _ _)
      ((a.wkAppend (Δ := Δ.cons ⟨A, q⟩) ⟨A, 0⟩).pwk ((Ctx?.PWk.refl _).cons (by simp)))

def Eqv.swapAppend {Γ Δ : Ctx? α} (a : Eqv R ((Γ ++ Δ).cons ⟨A, ⊤⟩) B)
  : Eqv R (Γ.cons ⟨A, ⊤⟩ ++ Δ) B
  := .let₁ (Γ.erase_right.right.append Δ.erase_right)
      (bvAppend _ _) (a.wkAppend (Δ := Δ.cons ⟨A, ⊤⟩) ⟨A, 0⟩)

-- def Eqv.revAppend {Γ Δ : Ctx? α} (a : Eqv R (Γ ++ Δ) A)
--   : Eqv R (Γ ++ Δ.rev) A := match Δ with
--   | .nil => a
--   | .cons Δ v => (a.swapAppend (Γ := Γ) (Δ := Δ)).revAppend.castCtx sorry

-- def Eqv.letPack {Γ Γl Γr Δ : Ctx? α}
--   (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr Δ.ety) (b : Eqv R (Γl ++ Δ) A) : Eqv R Γ A
--   := match Δ with
--   | .nil => sorry
--   | .cons Δ v => .let₂ hΓ a sorry
