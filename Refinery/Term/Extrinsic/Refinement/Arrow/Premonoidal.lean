import Refinery.Term.Extrinsic.Refinement.Arrow.Category
import Refinery.Term.Extrinsic.Wf.DerivedRewrite
import Discretion.Premonoidal.Category

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def DRWS.Arrow.whiskerLeft (A : R.Obj) (f : Arrow R B C) : Arrow R (A.tensor B) (A.tensor C)
  := Eqv.toArr (.let₂ (Ctx?.erase_left _) .bv0 (.pair
    ((Ctx?.erase_right _).cons (.right _))
    .bv1 (.letArrow .bv0 f)
  ))

def DRWS.Arrow.whiskerRight (f : Arrow R A B) (C : R.Obj) : Arrow R (A.tensor C) (B.tensor C)
  := Eqv.toArr (.let₂ (Ctx?.erase_left _) .bv0 (.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) .bv0
  ))

theorem DRWS.Obj.whiskerLeft_id (A : R.Obj) : A.id.whiskerLeft B = id (B.tensor A)
  := by simp [Arrow.whiskerLeft, Eqv.letArrow_id]; exact Eqv.let₂_eta _

theorem DRWS.Obj.id_whiskerRight (A : R.Obj) : A.id.whiskerRight B = id (A.tensor B)
  := by
  simp [Arrow.whiskerRight, Eqv.letArrow_id]
  convert Eqv.let₂_eta _ using 1
  apply Eqv.sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.letArrow_whiskerLeft
  (a : Eqv R Γ (A.tensor B)) (f : DRWS.Arrow R B C)
  : a.letArrow (f.whiskerLeft A) = .let₂ (Ctx?.erase_left _) a (.pair
    ((Ctx?.erase_right _).cons (.right _))
    .bv1 (.letArrow .bv0 f)
  ) := by
  apply Eq.symm
  convert a.bind_let₂ _ _
  induction a, f using quotInd₂
  apply sound; apply Wf.eqv.of_tm;
  simp only [
    Wf.let₁, Wf.wk, Wf.let₂, Wf.pair, Wf.bv1, Wf.bv0, Wf.wk2, Ctx?.extend1, Ctx?.Wk.ix,
    Ctx?.Wk.drop_ix, Ctx?.length
  ]
  simp [Ctx?.nil, Ctx?.cons, Ctx?.erase, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem Eqv.letArrow_whiskerRight
  (a : Eqv R Γ (A.tensor B)) (f : DRWS.Arrow R A C)
  : a.letArrow (f.whiskerRight B) = .let₂ (Ctx?.erase_left _) a (.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) .bv0
  ) := by
  apply Eq.symm
  convert a.bind_let₂ _ _
  induction a, f using quotInd₂
  apply sound; apply Wf.eqv.of_tm;
  simp only [
    Wf.let₁, Wf.wk, Wf.let₂, Wf.pair, Wf.bv1, Wf.bv0, Wf.wk2, Ctx?.extend1, Ctx?.Wk.ix,
    Ctx?.Wk.drop_ix, Ctx?.length
  ]
  simp [Ctx?.nil, Ctx?.cons, Ctx?.erase, ren_ren, <-Nat.liftWk_comp]
  rfl

-- theorem DRWS.Arrow.whiskerLeft_comp_whiskerLeft {A : R.Obj} (f : Arrow R B C) (g : Arrow R C D)
--   : (f.whiskerLeft A).comp (g.whiskerLeft A) = (f.comp g).whiskerLeft A
--   := by
--   rw [comp, Eqv.letArrow_whiskerLeft, whiskerLeft, Eqv.toEqv_toArr, Eqv.let₂_let₂, whiskerLeft]
--   congr 2
--   conv => rhs; rw [Eqv.bind_pair]
--   rw [Eqv.let₂_beta]
--   congr 1
--   simp only [
--     Eqv.wk0_letArrow, Eqv.wk0_bv0, Eqv.let_letArrow, comp, Eqv.toArr, extend1, Eqv.wk_letArrow,
--     toEqv
--   ]
--   congr 2
--   rw [bv0_letArrow']
--   conv => lhs;
--   induction g using Eqv.quotInd
--   apply Eqv.sound; apply Wf.eqv.of_tm
--   simp only [
--     Wf.let₁, Wf.wk, Wf.pair, Wf.wk1, Wf.bv1, Wf.wk2, Wf.bv0, Ctx?.extend1, Ctx?.Wk.drop_ix,
--     Ctx?.Wk.ix, Ctx?.length_erase, Ctx?.length_cons, Ctx?.length_nil, Nat.zero_add
--   ]
--   sorry

-- theorem DRWS.Arrow.whiskerLeft_comp {A : R.Obj} (f : Arrow R B C) (g : Arrow R C D)
--   : (f.comp g).whiskerLeft A = (f.whiskerLeft A).comp (g.whiskerLeft A)
--   := (f.whiskerLeft_comp_whiskerLeft g).symm

def DRWS.Obj.assoc (A B C : R.Obj) : Arrow R ((A.tensor B).tensor C) (A.tensor (B.tensor C))
  := Eqv.toArr (.let₂ (Ctx?.erase_left _) .bv0 (
    .let₂ ((Ctx?.erase_left _).cons (.left _)) .bv1 (.pair
      ((((Ctx?.erase_left _).cons (.right _)).cons (.left _)).cons (.right _))
      .bv1
      (.pair
        ((((Ctx?.erase_left _).cons (.right _)).cons (.left _)).cons (.left _))
        .bv0
        .bv2
      ))
  ))

def DRWS.Obj.assoc_inv (A B C : R.Obj) : Arrow R (A.tensor (B.tensor C)) ((A.tensor B).tensor C)
  := Eqv.toArr (.let₂ (Ctx?.erase_left _) .bv0 (
    .let₂ ((Ctx?.erase_right _).cons (.right _)) .bv0 (.pair
      ((Ctx?.erase_right _).cons (.right _))
      (.pair
        ((((Ctx?.erase_right _).cons (.right _)).cons (.right _)).cons (.left _))
        .bv3 .bv1)
      .bv0
    )))

def DRWS.Obj.leftUnitor (A : R.Obj) : Arrow R (.tensor .unit A) A
  := Eqv.toArr (.let₂ (Ctx?.erase_left _) .bv0 .bv0)

def DRWS.Obj.leftUnitor_inv (A : R.Obj) : Arrow R A (.tensor .unit A)
  := Eqv.toArr (.pair (Ctx?.erase_left _) (.unit _) .bv0)

def DRWS.Obj.rightUnitor (A : R.Obj) : Arrow R (A.tensor .unit) A
  := Eqv.toArr (.let₂ (Ctx?.erase_left _) .bv0 .bv1)

def DRWS.Obj.rightUnitor_inv (A : R.Obj) : Arrow R A (A.tensor .unit)
  := Eqv.toArr (.pair (Ctx?.erase_right _) .bv0 (.unit _))
