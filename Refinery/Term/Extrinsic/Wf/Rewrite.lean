import Refinery.Term.Extrinsic.Wf.Wk

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α} [R.UWkCongr]

def Wf.eqv.equivFwdStep
  {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) (h : (DRWS.EquivFwdStep (S := S)).rel a.deriv b.deriv)
  : a ≈ b := ⟨
    .base (.equiv (.fwd h)),
    .base (.equiv (.bwd h)),
  ⟩

def Eqv.let_op {Γ Γl Γr : Ctx? α} {f A B C}
    (hΓ : Γ.SSplit Γl Γr) (hf : S.FnTy f A B) (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
    : (a.op hf).let₁ hΓ b
    = a.let₁ hΓ (.let₁ (Γl.erase_right.cons (.right _)) (.op hf .bv0) (b.wk1 _)) := by
  induction a, b using quotInd₂
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_op

def Eqv.let_let₁ {Γ Γl Γc Γm Γr : Ctx? α} {A B C}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (a : Eqv R Γr A) (b : Eqv R (Γm.cons ⟨A, ⊤⟩) B) (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
    : (a.let₁ hΓc b).let₁ hΓ c
    = a.let₁ (hΓ.s1_23_12_3 hΓc) (b.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (c.wk1 _)) := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.eqv.equivFwdStep
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
  apply Wf.eqv.equivFwdStep
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
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_case

def Eqv.let_abort {Γ Γl Γr : Ctx? α} {A B}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr Ty.empty) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B)
    : ((a.abort _).let₁ hΓ b)
    = a.let₁ hΓ (.let₁ (Γl.erase_right.cons (.right _)) (.abort _ (.bv0)) (b.wk1 _)) := by
  induction a, b using quotInd₂ with
  | h a b => cases a with | mk a da => cases b with | mk b db =>
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.let_move
  apply DRWS.LetMove.let_abort

--TODO: backwards rules, with hax... that autocompleted to haxioms.

def Eqv.bind_op {Γ : Ctx? α} {f A B}
  (hf : S.FnTy f A B) (a : Eqv R Γ A)
  : a.op hf
    = a.let₁ Γ.erase_left (.op hf .bv0) := by
  induction a using quotInd
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.let_bind
  apply DRWS.LetBind.bind_op


def Eqv.bind_let₂ {Γ Γl Γr : Ctx? α} {A B C}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.tensor B))
  (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : (a.let₂ hΓ b)
  = a.let₁ hΓ (.let₂ (Γl.erase_right.cons (.right _)) .bv0 (b.wk2 _)) := by
  induction a, b using quotInd₂
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.let_bind
  apply DRWS.LetBind.bind_let₂

def Eqv.bind_case {Γ Γl Γr : Ctx? α} {A B C}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.coprod B))
  (b : Eqv R (Γl.cons ⟨A, ⊤⟩) C)
  (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
  : (a.case hΓ b c)
  = a.let₁ hΓ (.case (Γl.erase_right.cons (.right _)) .bv0 (b.wk1 _) (c.wk1 _)) := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.let_bind
  apply DRWS.LetBind.bind_case

def Eqv.bind_iter {Γ Γl Γr : Ctx? α} {A B : Ty α}
  (hΓ : Γ.SSplit Γl Γr) (hc : Γl.copy) (hd : Γl.del)
  (a : Eqv R Γr A)
  (b : Eqv R (Γl.cons ⟨A, ⊤⟩) (B.coprod A))
  : (a.iter hΓ b)
  = a.let₁ hΓ (.iter (Γl.erase_right.cons (.right _)) .bv0 (b.wk1 _)) := by
  induction a, b using quotInd₂
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.let_bind
  apply DRWS.LetBind.bind_iter

def Eqv.terminal {Γ : Ctx? α} (a : Eqv R Γ Ty.unit)
  : (a.let₁ Γ.erase_left (.unit _))
  = a := by
  induction a using quotInd
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.terminal

def Eqv.initial {Γ Γl Γr : Ctx? α} {B}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr Ty.empty)
  (b c : Eqv R (Γl.cons ⟨Ty.empty, ⊤⟩) B)
  : a.let₁ hΓ b = a.let₁ hΓ c := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.initial

def Eqv.let₂_eta {Γ : Ctx? α} {A B : Ty α}
  (a : Eqv R Γ (A.tensor B))
  : a.let₂ Γ.erase_left (.pair (((Γ.erase.both).cons (.left _)).cons (.right _)) .bv1 .bv0)
  = a := by
  induction a using quotInd
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.let₂_eta

def Eqv.case_eta {Γ : Ctx? α} {A B : Ty α}
  (a : Eqv R Γ (A.coprod B))
  : a.case Γ.erase_left (.inl _ _ .bv0) (.inr _ _ .bv0) = a := by
  induction a using quotInd
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.case_eta

def Eqv.let₂_beta {Γ Γc Γl Γm Γr : Ctx? α} {A B C}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γm A) (b : Eqv R Γr B)
  (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : ((a.pair hΓc b).let₂ hΓ c)
  = a.let₁ (hΓ.s1_23_13_2 hΓc)
      ((b.wk0 _).let₁ ((hΓ.s1_23_13 hΓc).cons (.left _)) c) := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.let₂_beta

def Eqv.case_inl {Γ Γl Γr : Ctx? α} {A B C}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr A)
  (b : Eqv R (Γl.cons ⟨A, ⊤⟩) C)
  (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
  : ((a.inl _ _).case hΓ b c) = a.let₁ hΓ b := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.case_inl

def Eqv.case_inr {Γ Γl Γr : Ctx? α} {A B C}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr B)
  (b : Eqv R (Γl.cons ⟨A, ⊤⟩) C)
  (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
  : ((a.inr _ _).case hΓ b c) = a.let₁ hΓ c := by
  induction a, b, c using quotInd₃
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.case_inr

def Eqv.fixpoint {Γ Γl Γr : Ctx? α} {A B : Ty α}
  (hΓ : Γ.SSplit Γl Γr) (hc : Γl.copy) (hd : Γl.del)
  (a : Eqv R Γr A)
  (b : Eqv R (Γl.cons ⟨A, ⊤⟩) (B.coprod A))
  : a.iter hΓ b
  = a.let₁ hΓ (.case (Γl.both.cons (.right _)) b .bv0
    (.iter ((Γl.erase_right.cons (.right _)).cons (.right _)) .bv0 ((b.wk1 _).wk1 _))) := by
  induction a, b using quotInd₂
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.fixpoint

def Eqv.codiag {Γ Γl Γr : Ctx? α} {A B : Ty α}
  (hΓ : Γ.SSplit Γl Γr) (hc : Γl.copy) (hd : Γl.del)
  (a : Eqv R Γr A)
  (b : Eqv R (Γl.cons ⟨A, ⊤⟩) ((B.coprod A).coprod A))
  : a.iter hΓ (b.case (Γl.erase_left.cons (.right _)) .bv0 (.inr _ _ .bv0))
  = a.iter hΓ
      (.iter (Γl.erase_right.cons (.right _)) .bv0 (b.wk1 _)) := by
  induction a, b using quotInd₂
  apply sound
  apply Wf.eqv.equivFwdStep
  apply DRWS.EquivFwdStep.step
  apply DRWS.Step.codiag
