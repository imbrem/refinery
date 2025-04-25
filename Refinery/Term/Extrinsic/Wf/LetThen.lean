import Refinery.Term.Extrinsic.Wf.Rewrite

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
