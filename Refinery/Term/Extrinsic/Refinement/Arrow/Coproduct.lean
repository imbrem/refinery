import Refinery.Term.Extrinsic.Refinement.Arrow.Category
import Discretion.ChosenFiniteCoproducts

open HasQuant HasPQuant HasCommRel

open CategoryTheory

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def DRWS.from0 (R : DRWS φ α) (A : Ty α) : Arrow R .empty A := (Eqv.bv0.abort A).toArr

--TODO: from0 initial

def DRWS.inlArr (R : DRWS φ α) (A B : Ty α) : Arrow R A (A.coprod B) := (Eqv.bv0.inl A B).toArr

def DRWS.inrArr (R : DRWS φ α) (A B : Ty α) : Arrow R B (A.coprod B) := (Eqv.bv0.inr A B).toArr

def DRWS.Arrow.coprodOut {A B C D : Ty α}
  (f : Arrow R A (B.coprod C)) (g : Arrow R B D) (h : Arrow R C D) : Arrow R A D
  := (Eqv.case (Ctx?.erase_left _) f.toEqv (g.extend1 _) (h.extend1 _)).toArr

def DRWS.Arrow.coprod {A B C : Ty α} (f : Arrow R A C) (g : Arrow R B C)
  : Arrow R (A.coprod B) C := (R.idArr _).coprodOut f g

def DRWS.Arrow.sumOut {A B C X Y : Ty α}
  (f : Arrow R A (B.coprod C)) (g : Arrow R B X) (h : Arrow R C Y) : Arrow R A (X.coprod Y)
  := (Eqv.case (Ctx?.erase_left _) f.toEqv ((g.extend1 _).inl _ _) ((h.extend1 _).inr _ _)).toArr

def DRWS.Arrow.sum {A B C D : Ty α}
  (f : Arrow R A C) (g : Arrow R B D) : Arrow R (A.coprod B) (C.coprod D)
  := (R.idArr _).sumOut f g

theorem DRWS.Arrow.comp_coprod {A B C D : Ty α}
  (f : Arrow R A (B.coprod C)) (g : Arrow R B D) (h : Arrow R C D)
  : f.comp (g.coprod h) = f.coprodOut g h := by
  simp only [comp, coprodOut, Eqv.letArrow]
  rw [Eqv.bind_case]
  induction f, g, h using Eqv.quotInd₃
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp
  [Wf.let₁, Wf.wk, Wf.case, PreArrow.refl, Wf.bv0, Ctx?.extend1, Wf.wk1, ren_ren, <-Nat.liftWk_comp]
  constructor <;> rfl

theorem DRWS.Arrow.comp_coprodOut {X A B C D : Ty α}
  (x : Arrow R X A) (f : Arrow R A (B.coprod C)) (g : Arrow R B D) (h : Arrow R C D)
  : (x.comp (f.coprodOut g h)) = (x.comp f).coprodOut g h := by
  rw [<-comp_coprod, <-comp_coprod, comp_assoc]

-- theorem DRWS.Arrow.comp_inl {A B C : Ty α} (f : Arrow R A B)
--   : f.comp (R.inlArr B C) = f.toEqv.inl _ _ := sorry

-- theorem DRWS.Arrow.comp_inr {A B C : Ty α} (f : Arrow R A C)
--   : f.comp (R.inrArr B C) = f.toEqv.inr _ _ := sorry

--TODO: coprodOut comp_inl comp_inr is sumOut

--TODO: therefore coprod comp_inl comp_inr is sum

--TODO: sum id id is id; coprod comp_inl comp_inr is id

--TODO: comp sum is sumOut

--TODO: comp_sumOut

theorem DRWS.Arrow.inl_coprod {A B C : Ty α} (f : Arrow R A C) (g : Arrow R B C)
  : (DRWS.inlArr R A B).comp (DRWS.Arrow.coprod f g) = f := by
  simp only [comp_coprod, coprodOut, inlArr, Eqv.toArr, toEqv, Eqv.case_inl]
  exact f.let₁_bv0

theorem DRWS.Arrow.inr_coprod {A B C : Ty α} (f : Arrow R A C) (g : Arrow R B C)
  : (DRWS.inrArr R A B).comp (DRWS.Arrow.coprod f g) = g := by
  simp only [comp_coprod, coprodOut, inrArr, Eqv.toArr, toEqv, Eqv.case_inr]
  exact g.let₁_bv0

instance DRWS.coproducts : ChosenFiniteCoproducts (Obj R) where
  coproduct := sorry
  initial := sorry

end Term

end Refinery
