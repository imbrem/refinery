import Refinery.Term.Extrinsic.Wf.DerivedRewrite

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def Eqv.swap0 {Γ : Ctx? α} {A B : Ty α} {x : Var? α}
  (a : Eqv R ((Γ.cons x).cons ⟨A, ⊤⟩) B) : Eqv R ((Γ.cons ⟨A, ⊤⟩).cons x) B
  := .let₁ (Ctx?.erase_right _).right.left .bv1 (a.wk2 (x := ⟨A, 0⟩))

def Eqv.swap0_swap0 {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R ((Γ.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) : a.swap0.swap0 = a
  := calc
  _ = Eqv.let₁ (Ctx?.erase_right _).right .bv0 (a.wk1 (x := ⟨B, 0⟩))
    := by
      induction a using quotInd with
      | h a =>
      apply sound
      apply Wf.eqv.coh_out
      apply Wf.pre_beta_pureIIn
      simp
      simp [Wf.wk2, Wf.subst, Wf.let₁, Wf.wk1, Wf.bv0, Wf.bv1]
      constructor
      rfl
      rw [<-subst_renIn, <-subst_renIn, <-subst_ofRen]
      apply Subst.subst_eqOn_fvi
      intro x hx
      simp [Subst.renIn, Subst.ofRen]
      cases x using Nat.cases2 with
      | zero => rfl
      | one => rfl
      | rest x =>
        simp [SubstDS.refl_get]
        split
        rfl
        have ha := a.deriv.fvi_le_length
        simp at ha
        omega
  _ = _
    := by
    conv => rhs; rw [<-a.let₁_bv0]
    induction a using quotInd
    exact of_tm rfl

theorem Eqv.swap0_injective {Γ : Ctx? α} {A B C : Ty α}
  (a b : Eqv R ((Γ.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (h : a.swap0 = b.swap0) : a = b
  := by rw [<-a.swap0_swap0, <-b.swap0_swap0, h]
