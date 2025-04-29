import Refinery.Term.Extrinsic.Wf.DerivedRewrite

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

def Eqv.letT₁ {Γ : Ctx? α} {A B : Ty α} (a : Eqv R Γ A) (b : Eqv R (Γ.erase.cons ⟨A, ⊤⟩) B) :
  Eqv R Γ B := a.let₁ Γ.erase_left b

def Eqv.letT₂ {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (.tensor A B)) (b : Eqv R ((Γ.erase.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) :
  Eqv R Γ C := a.let₂ Γ.erase_left b

def Eqv.caseT {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (.coprod A B))
  (b : Eqv R (Γ.erase.cons ⟨A, ⊤⟩) C) (c : Eqv R (Γ.erase.cons ⟨B, ⊤⟩) C) :
  Eqv R Γ C := a.case Γ.erase_left b c

def Eqv.iterT {Γ : Ctx? α} {A B : Ty α}
  (a : Eqv R Γ A)
  (b : Eqv R ((Γ.erase.cons ⟨A, ⊤⟩)) (.coprod B A)) :
  Eqv R Γ B := a.iter Γ.erase_left b

def Eqv.letT₂_eta {Γ : Ctx? α} {A B : Ty α}
  (a : Eqv R Γ (A.tensor B))
  : a.letT₂ (.pair (((Γ.erase.both).cons (.left _)).cons (.right _)) .bv1 .bv0)
  = a := a.let₂_eta

variable [R.UWkCongr]

theorem Eqv.letT₂_letT₂ {Γ : Ctx? α} {A B C D E : Ty α}
  (a : Eqv R Γ (A.tensor B))
  (b : Eqv R ((Γ.erase.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor D))
  (c : Eqv R ((Γ.erase.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
  : (a.letT₂ b).letT₂ c
  = a.letT₂ (b.letT₂ (((c.castCtx (by (conv => lhs; rw [<-Ctx?.erase_erase]); rfl)).wk2 _).wk2 _))
  := by
  rw [letT₂, letT₂, let₂_let₂]
  induction a, b, c using quotInd₃
  exact of_tm rfl

theorem Eqv.letT₂_beta  {Γ Γl Γr : Ctx? α} {A B}
  (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B)
  (c : Eqv R ((Γ.erase.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : letT₂ (pair hΓ a b) c = .let₁ hΓ.comm a (.let₁ (Ctx?.erase_left _).left (b.wk0 _)
    (c.castCtx (by rw [hΓ.erase_eq_right]))) := by
  rw [letT₂, let₂_beta]
  induction a, b, c using quotInd₃
  exact of_tm rfl
