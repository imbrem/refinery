import Refinery.Term.Extrinsic.Refinement.Arrow.Category
import Refinery.Term.Extrinsic.Wf.DerivedRewrite
import Refinery.Term.Extrinsic.Wf.Assoc
import Discretion.Premonoidal.Category

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def DRWS.Arrow.whiskerLeft (A : R.Obj) (f : Arrow R B C) : Arrow R (A.tensor B) (A.tensor C)
  := Eqv.toArr (.letT₂ .bv0 (.pair
    ((Ctx?.erase_right _).cons (.right _))
    .bv1 (.letArrow .bv0 f)
  ))

def DRWS.Arrow.whiskerRight (f : Arrow R A B) (C : R.Obj) : Arrow R (A.tensor C) (B.tensor C)
  := Eqv.toArr (.letT₂ .bv0 (.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) .bv0
  ))

def DRWS.Arrow.tensorHom (f : Arrow R A B) (g : Arrow R A' B')
  : Arrow R (A.tensor A') (B.tensor B')
  := Eqv.toArr (.letT₂ .bv0 (.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) (.letArrow .bv0 g)
  ))

def DRWS.Obj.leftUnitor (A : R.Obj) : Arrow R (.tensor .unit A) A
  := Eqv.toArr (Eqv.bv0.releft)

def DRWS.Obj.leftUnitor_inv (A : R.Obj) : Arrow R A (.tensor .unit A)
  := Eqv.toArr (Eqv.bv0.releft_inv)

theorem Eqv.letArrow_leftUnitor {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (.tensor .unit A)) : a.letArrow (DRWS.Obj.leftUnitor A) = a.releft
  := by
  rw [releft, letT₂, bind_let₂]
  induction a using quotInd
  exact Eqv.of_tm rfl

theorem Eqv.letArrow_leftUnitor_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : a.letArrow (DRWS.Obj.leftUnitor_inv A) = a.releft_inv
  := by
  rw [releft_inv, bind_pair_right _ ⊥ ⊤]
  induction a using quotInd
  exact Eqv.of_tm rfl
  apply HasCommRel.commutes_bot_left

theorem DRWS.Obj.leftUnitor_leftUnitor_inv {A : R.Obj}
  : A.leftUnitor.comp A.leftUnitor_inv = id (.tensor .unit A) := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_leftUnitor_inv, leftUnitor, Eqv.releft_releft_inv]
  rfl

theorem DRWS.Obj.leftUnitor_inv_leftUnitor {A : R.Obj}
  : A.leftUnitor_inv.comp A.leftUnitor = id A := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_leftUnitor, leftUnitor_inv, Eqv.releft_inv_releft]
  rfl

def DRWS.Obj.rightUnitor (A : R.Obj) : Arrow R (A.tensor .unit) A
  := Eqv.toArr (Eqv.bv0.reright)

def DRWS.Obj.rightUnitor_inv (A : R.Obj) : Arrow R A (A.tensor .unit)
  := Eqv.toArr (Eqv.bv0.reright_inv)

theorem Eqv.letArrow_rightUnitor {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (A.tensor .unit)) : a.letArrow (DRWS.Obj.rightUnitor A) = a.reright
  := by
  rw [reright, letT₂, bind_let₂]
  induction a using quotInd
  exact Eqv.of_tm rfl

theorem Eqv.letArrow_rightUnitor_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : a.letArrow (DRWS.Obj.rightUnitor_inv A) = a.reright_inv
  := by
  rw [reright_inv, bind_pair_left]
  induction a using quotInd
  exact Eqv.of_tm rfl

theorem DRWS.Obj.rightUnitor_rightUnitor_inv {A : R.Obj}
  : A.rightUnitor.comp A.rightUnitor_inv = id (A.tensor .unit) := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_rightUnitor_inv, rightUnitor, Eqv.reright_inv_reright]
  rfl

theorem DRWS.Obj.rightUnitor_inv_rightUnitor {A : R.Obj}
  : A.rightUnitor_inv.comp A.rightUnitor = id A := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_rightUnitor, rightUnitor_inv, Eqv.reright_reright_inv]
  rfl


def DRWS.Obj.assoc (A B C : R.Obj) : Arrow R ((A.tensor B).tensor C) (A.tensor (B.tensor C))
  := Eqv.toArr (.reassoc .bv0)

def DRWS.Obj.assoc_inv (A B C : R.Obj) : Arrow R (A.tensor (B.tensor C)) ((A.tensor B).tensor C)
  := Eqv.toArr (.reassoc_inv .bv0)

theorem Eqv.letArrow_assoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : a.letArrow (DRWS.Obj.assoc A B C) = a.reassoc
  := by
  rw [reassoc, letT₂, bind_let₂]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₁, Var?.erase_erase, Wf.bv1, Wf.pair, Wf.wk, let₁.injEq, true_and, Wf.let₂, Wf.bv0,
    Wf.wk2, Wf.bv2]
  simp [ren_ren, Ctx?.extend1]

theorem Eqv.letArrow_assoc_inv {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : a.letArrow (DRWS.Obj.assoc_inv A B C) = a.reassoc_inv
  := by
  rw [reassoc_inv, bind_let₂]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₁, Var?.erase_erase, Wf.bv1, Wf.pair, Wf.wk, let₁.injEq, true_and, Wf.let₂, Wf.bv0,
    Wf.wk2, Wf.bv2, Wf.bv3]
  simp [ren_ren, Ctx?.extend1]
  
theorem DRWS.Obj.assoc_comp_assoc_inv {A B C : R.Obj}
  : (DRWS.Obj.assoc A B C).comp (DRWS.Obj.assoc_inv A B C) = id ((A.tensor B).tensor C) := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_assoc_inv, DRWS.Obj.assoc, Eqv.reassoc_inv_reassoc]
  rfl

theorem DRWS.Obj.assoc_inv_comp_assoc {A B C : R.Obj}
  : (DRWS.Obj.assoc_inv A B C).comp (DRWS.Obj.assoc A B C) = id (A.tensor (B.tensor C)) := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_assoc, DRWS.Obj.assoc_inv, Eqv.reassoc_reassoc_inv]
  rfl

open CategoryTheory

instance DRWS.Obj.instMonoidalCategoryStruct : MonoidalCategoryStruct R.Obj where
  tensorObj A B := A.tensor B
  tensorUnit := .unit
  tensorHom f g := f.tensorHom g
  whiskerLeft A _ _ f := f.whiskerLeft A
  whiskerRight f B := f.whiskerRight B
  associator A B C :=
    ⟨A.assoc B C, A.assoc_inv B C, DRWS.Obj.assoc_comp_assoc_inv, DRWS.Obj.assoc_inv_comp_assoc⟩
  leftUnitor A :=
    ⟨A.leftUnitor, A.leftUnitor_inv,
      DRWS.Obj.leftUnitor_leftUnitor_inv, DRWS.Obj.leftUnitor_inv_leftUnitor⟩
  rightUnitor A :=
    ⟨A.rightUnitor, A.rightUnitor_inv,
      DRWS.Obj.rightUnitor_rightUnitor_inv, DRWS.Obj.rightUnitor_inv_rightUnitor⟩
