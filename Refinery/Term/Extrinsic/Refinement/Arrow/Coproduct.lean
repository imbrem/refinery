import Refinery.Term.Extrinsic.Refinement.Arrow.Category
import Discretion.ChosenFiniteCoproducts

open HasQuant HasPQuant HasCommRel

open CategoryTheory Limits

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def DRWS.zeroObj (R : DRWS φ α) : R.Obj := .empty

def DRWS.Obj.from0 (A : R.Obj) : Arrow R R.zeroObj A := (Eqv.bv0.abort A).toArr

theorem DRWS.Arrow.from0_uniq {A : R.Obj} (f g : Arrow R R.zeroObj A) : f = g := by
  apply Eq.trans f.let₁_bv0.symm
  apply Eq.trans _ g.let₁_bv0
  apply Eqv.initial

theorem DRWS.Arrow.from0_comp {A B : R.Obj} (f : Arrow R A B) : A.from0.comp f = B.from0
  := from0_uniq _ _

theorem DRWS.Arrow.from0_eq {A : R.Obj} (f : Arrow R R.zeroObj A) : f = A.from0
  := from0_uniq _ _

def DRWS.Obj.inl (A B : R.Obj) : Arrow R A (A.coprod B) := (Eqv.bv0.inl A B).toArr

def DRWS.Obj.inr (A B : R.Obj) : Arrow R B (A.coprod B) := (Eqv.bv0.inr A B).toArr

def DRWS.Arrow.coprodOut {A B C D : Ty α}
  (f : Arrow R A (B.coprod C)) (g : Arrow R B D) (h : Arrow R C D) : Arrow R A D
  := (Eqv.case (Ctx?.erase_left _) f.toEqv (g.extend1 _) (h.extend1 _)).toArr

def DRWS.Arrow.coprod {A B C : Ty α} (f : Arrow R A C) (g : Arrow R B C)
  : Arrow R (A.coprod B) C := (Obj.id _).coprodOut f g

def DRWS.Arrow.sumOut {A B C X Y : Ty α}
  (f : Arrow R A (B.coprod C)) (g : Arrow R B X) (h : Arrow R C Y) : Arrow R A (X.coprod Y)
  := (Eqv.case (Ctx?.erase_left _) f.toEqv ((g.extend1 _).inl _ _) ((h.extend1 _).inr _ _)).toArr

def DRWS.Arrow.sum {A B C D : Ty α}
  (f : Arrow R A C) (g : Arrow R B D) : Arrow R (A.coprod B) (C.coprod D)
  := (Obj.id _).sumOut f g

theorem Eqv.letArrow_coprod {A B C : Ty α}
  (a : Eqv R Γ (A.coprod B)) (f : DRWS.Arrow R A C) (g : DRWS.Arrow R B C)
  : a.letArrow (f.coprod g) = a.case Γ.erase_left (f.extend1 _) (g.extend1 _)
  := by
  simp only [DRWS.Arrow.coprod, DRWS.Arrow.coprodOut, Eqv.letArrow]
  conv => rhs; rw [Eqv.bind_case]
  induction a, f, g using Eqv.quotInd₃
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [
    Wf.let₁, Wf.wk, Wf.case, DRWS.PreArrow.refl, Wf.bv0, Ctx?.extend1, Wf.wk1, ren_ren,
    <-Nat.liftWk_comp
  ]
  constructor <;> rfl

theorem DRWS.Arrow.comp_coprod {A B C D : Ty α}
  (f : Arrow R A (B.coprod C)) (g : Arrow R B D) (h : Arrow R C D)
  : f.comp (g.coprod h) = f.coprodOut g h := f.letArrow_coprod g h

theorem Eqv.letArrow_coprodOut {A B C D : Ty α}
  (a : Eqv R Γ A) (f : DRWS.Arrow R A (B.coprod C)) (g : DRWS.Arrow R B D) (h : DRWS.Arrow R C D)
  : a.letArrow (f.coprodOut g h) = (a.letArrow f).case Γ.erase_left (g.extend1 _) (h.extend1 _)
  := by rw [<-DRWS.Arrow.comp_coprod, letArrow_comp, letArrow_coprod]

theorem DRWS.Arrow.comp_coprodOut {X A B C D : Ty α}
  (x : Arrow R X A) (f : Arrow R A (B.coprod C)) (g : Arrow R B D) (h : Arrow R C D)
  : (x.comp (f.coprodOut g h)) = (x.comp f).coprodOut g h := by
  rw [<-comp_coprod, <-comp_coprod, comp_assoc]

theorem Eqv.letArrow_inl (f : Eqv R Γ A) : f.letArrow (DRWS.Obj.inl A B) = f.inl A B
  := f.bind_inl

theorem Eqv.letArrow_inr (f : Eqv R Γ B) : f.letArrow (DRWS.Obj.inr A B) = f.inr A B
  := f.bind_inr

theorem DRWS.Arrow.comp_inl {A B C : Ty α} (f : Arrow R A B)
  : f.comp (Obj.inl B C) = f.toEqv.inl _ _ := f.bind_inl

theorem DRWS.Arrow.comp_inr {A B C : Ty α} (f : Arrow R A C)
  : f.comp (Obj.inr B C) = f.toEqv.inr _ _ := f.bind_inr

theorem DRWS.Arrow.coprodOut_inl_inr {X A B : Ty α}
  (x : Arrow R X (A.coprod B)) : x.coprodOut (Obj.inl A B) (Obj.inr A B) = x
  := x.case_eta

theorem DRWS.Arrow.coprod_inl_inr {A B : Ty α}
  : (Obj.inl A B).coprod (Obj.inr A B) = Obj.id (R := R) (A.coprod B)
  := (Obj.id (A.coprod B)).coprodOut_inl_inr

theorem Eqv.letArrow_case {Γ Γl Γr : Ctx? α} {A B C D : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.coprod B)) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) C) (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
  (f : DRWS.Arrow R C D)
  : (a.case hΓ b c).letArrow f = a.case hΓ (b.letArrow f) (c.letArrow f)
  := by
  rw [letArrow, letT₁, let_case]
  induction a, b, c, f using Eqv.quotInd₄
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [
    Wf.case, Wf.wk, Wf.let₁, Ctx?.extend1, Wf.wk1, ren_ren, Ctx?.Wk.drop_ix, hΓ.left_length,
    <-Nat.liftWk_comp, Nat.stepWk
  ]

theorem DRWS.Arrow.coprodOut_comp {A B C D Y : Ty α}
  (f : Arrow R A (B.coprod C)) (g : Arrow R B D) (h : Arrow R C D) (y : Arrow R D Y)
  : (f.coprodOut g h).comp y = f.coprodOut (g.comp y) (h.comp y)
  := by
  convert Eqv.letArrow_case _ _ _ _ _
  induction f, g, h, y using Eqv.quotInd₄
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [Wf.case, Wf.wk, Wf.let₁, Ctx?.extend1, Wf.wk1, ren_ren, Ctx?.Wk.drop_ix, <-Nat.liftWk_comp]
  rfl

theorem DRWS.Arrow.coprod_comp {A B C D : Ty α}
  (f : Arrow R A C) (g : Arrow R B C) (h : Arrow R C D)
  : (f.coprod g).comp h = (f.comp h).coprod (g.comp h) := coprodOut_comp _ f g h

theorem DRWS.Arrow.coprod_self {A B C : Ty α}
  (f : Arrow R (A.coprod B) C)
  : ((Obj.inl A B).comp f).coprod ((Obj.inr A B).comp f) = f
  := by rw [<-coprod_comp, coprod_inl_inr, id_comp]

theorem DRWS.Arrow.coprod_ext {A B C : Ty α}
  (f g : Arrow R (A.coprod B) C)
  (hl : (Obj.inl A B).comp f = (Obj.inl A B).comp g)
  (hr : (Obj.inr A B).comp f = (Obj.inr A B).comp g)
  : f = g := by rw [<-f.coprod_self, <-g.coprod_self, hl, hr]

--TODO: coprodOut comp_inl comp_inr is sumOut

--TODO: therefore coprod comp_inl comp_inr is sum

--TODO: sum id id is id; coprod comp_inl comp_inr is id

--TODO: comp sum is sumOut

--TODO: comp_sumOut

@[simp]
theorem DRWS.Arrow.inl_coprod {A B C : Ty α} (f : Arrow R A C) (g : Arrow R B C)
  : (Obj.inl A B).comp (DRWS.Arrow.coprod f g) = f := by
  simp only [comp_coprod, coprodOut, Obj.inl, Eqv.toArr, toEqv, Eqv.case_inl]
  exact f.let₁_bv0

@[simp]
theorem DRWS.Arrow.inr_coprod {A B C : Ty α} (f : Arrow R A C) (g : Arrow R B C)
  : (Obj.inr A B).comp (DRWS.Arrow.coprod f g) = g := by
  simp only [comp_coprod, coprodOut, Obj.inr, Eqv.toArr, toEqv, Eqv.case_inr]
  exact g.let₁_bv0

instance DRWS.coproducts : ChosenFiniteCoproducts (Obj R) where
  coproduct A B := {
    cocone := { pt := A.coprod B, ι := mapPair (Obj.inl A B) (Obj.inr A B) }
    isColimit := {
      desc s := Arrow.coprod (s.ι.app ⟨.left⟩) (s.ι.app ⟨.right⟩),
      uniq s m j := Arrow.coprod_ext _ _ (by convert j ⟨.left⟩; simp) (by convert j ⟨.right⟩; simp)
      fac s j := by cases j with | mk j => cases j <;> simp [Arrow.comp_def]
    }
  }
  initial := {
    cocone := { pt := R.zeroObj, ι := { app | ⟨X⟩ => X.elim } }
    isColimit := { desc s := s.pt.from0, uniq _ _ _ := Arrow.from0_uniq _ _ }
  }

end Term

end Refinery
