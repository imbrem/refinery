import Refinery.Term.Extrinsic.Refinement.Wk.Relation
import Refinery.Term.Extrinsic.Wf.Wk

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term


variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α}

def Wf.equiv_of_equivFwdStep
  {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) (h : (DRWS.EquivFwdStep (S := S)).rel a.deriv b.deriv)
  : a ≈ b := ⟨
    .base (.equiv (.fwd h)),
    .base (.equiv (.bwd h)),
  ⟩

variable  [R.UWkCongr]

def Eqv.let_op {Γ Γl Γr : Ctx? α} {f A B C}
    (hΓ : Γ.SSplit Γl Γr) (hf : S.FnTy f A B) (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
    : (a.op hf).let₁ hΓ b
    = a.let₁ hΓ (.let₁ (Γl.erase_right.cons (.right _)) (.op hf .bv0) (b.wk1 _)) := by
  induction a, b using quotInd₂
  apply sound
  apply Wf.equiv_of_equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_op

def Eqv.let_let₁ {Γ Γl Γc Γm Γr : Ctx? α} {A B C}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (a : Eqv R Γr A) (b : Eqv R (Γm.cons ⟨A, ⊤⟩) B) (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
    : (a.let₁ hΓc b).let₁ hΓ c
    = a.let₁ (hΓ.s1_23_12_3 hΓc) (b.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (c.wk1 _)) := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.equiv_of_equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_let₁

def Eqv.let_let₂ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (c : Eqv R (Γl.cons ⟨C, ⊤⟩) D)
    : (a.let₂ hΓc b).let₁ hΓ c
    = a.let₂ (hΓ.s1_23_12_3 hΓc)
      (b.let₁ (((hΓ.s1_23_12 hΓc).cons (.right _)).cons (.right _)) ((c.wk1 _).wk1 _)) := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.equiv_of_equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_let₂

def Eqv.let_case {Γ Γl Γc Γm Γr : Ctx? α} {A B C D}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (a : Eqv R Γr (A.coprod B)) (b : Eqv R (Γm.cons ⟨A, ⊤⟩) C)
    (c : Eqv R (Γm.cons ⟨B, ⊤⟩) C) (d : Eqv R (Γl.cons ⟨C, ⊤⟩) D)
    : (a.case hΓc b c).let₁ hΓ d
    = a.case (hΓ.s1_23_12_3 hΓc) (b.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (d.wk1 _))
                                 (c.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (d.wk1 _)) := by
  induction a, b, c, d using quotInd₄
  apply sound
  apply Wf.equiv_of_equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_case

def Eqv.let_abort {Γ Γl Γr : Ctx? α} {A B}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr Ty.empty) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B)
    : ((a.abort _).let₁ hΓ b)
    = a.let₁ hΓ (.let₁ (Γl.erase_right.cons (.right _)) (.abort _ (.bv0)) (b.wk1 _)) := by
  induction a, b using quotInd₂ with
  | h a b => cases a with | mk a da => cases b with | mk b db =>
  apply sound
  apply Wf.equiv_of_equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_abort

--TODO: backwards rules, with hax... that autocompleted to haxioms.
