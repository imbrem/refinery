import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Structure

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

theorem DRWS.Obj.whiskerLeft_id (A : R.Obj) : A.id.whiskerLeft B = id (B.tensor A)
  := by simp [Arrow.whiskerLeft, Eqv.letT₂, Eqv.letArrow_id]; exact Eqv.let₂_eta _

theorem DRWS.Obj.id_whiskerRight (A : R.Obj) : A.id.whiskerRight B = id (A.tensor B)
  := by
  simp [Arrow.whiskerRight, Eqv.letArrow_id]
  convert Eqv.let₂_eta _ using 1
  apply Eqv.sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.letArrow_whiskerLeft
  (a : Eqv R Γ (A.tensor B)) (f : DRWS.Arrow R B C)
  : a.letArrow (f.whiskerLeft A) = .letT₂ a (.pair
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
  : a.letArrow (f.whiskerRight B) = .letT₂ a (.pair
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

theorem DRWS.Arrow.whiskerLeft_comp_whiskerLeft {A : R.Obj}
  (f : Arrow R B C) (g : Arrow R C D)
  : (f.whiskerLeft A).comp (g.whiskerLeft A) = (f.comp g).whiskerLeft A
  := by
  rw [
    comp, Eqv.letArrow_whiskerLeft, whiskerLeft, Eqv.toEqv_toArr, Eqv.letT₂, Eqv.letT₂,
    Eqv.let₂_let₂, whiskerLeft]
  congr 2
  conv => rhs; rw [Eqv.bind_pair]
  rw [Eqv.let₂_beta]
  congr 1
  simp only [
    Eqv.wk0_letArrow, Eqv.wk0_bv0, Eqv.let_letArrow, comp, Eqv.toArr, extend1, Eqv.wk_letArrow,
    toEqv
  ]
  congr 2
  rw [bv0_letArrow']
  conv => lhs;
  simp only [Eqv.wk2_pair, Eqv.wk1_pair, Eqv.wk1_bv1, Eqv.wk2_bv1, Eqv.wk1_bv0]
  apply Eq.symm
  generalize (Ctx?.SSplit.cons (α := α) _ _) = hΓ₁
  generalize (Ctx?.SSplit.cons (α := α) _ _) = hΓ₂
  generalize (Ctx?.SSplit.cons (α := α) _ _) = hΓ₃
  generalize hρ : (Ctx?.extend1 (hΓ := _) (α := α) _ _) = ρ
  induction f, g using Eqv.quotInd₂ with
  | h f g =>
  apply Eqv.sound
  apply ((g.wk ρ).pre_beta_pureLout hΓ₁
    (Wf.pair (.cons (.cons (.cons (Ctx?.erase_right _) (.left _)) (.left _)) (.right _))
      .bv3 .bv0) (hb := _)).coh
  rfl
  simp [
    Wf.pair, Wf.wk1, Wf.subst, Wf.wk, Wf.bv3, Wf.bv2, Wf.wk2, SubstDS.refl_get, Wf.bv0,
    Ctx?.extend1, ren_ren, <-Nat.liftWk_comp, <-hρ
  ]
  rfl
  reduce
  infer_instance

theorem DRWS.Arrow.whiskerLeft_comp {A : R.Obj} (f : Arrow R B C) (g : Arrow R C D)
  : (f.comp g).whiskerLeft A = (f.whiskerLeft A).comp (g.whiskerLeft A)
  := (f.whiskerLeft_comp_whiskerLeft g).symm

theorem DRWS.Arrow.whiskerRight_comp_whiskerRight {A : R.Obj}
  (f : Arrow R B C) (g : Arrow R C D)
  : (f.whiskerRight A).comp (g.whiskerRight A) = (f.comp g).whiskerRight A := by
  rw [
    comp, Eqv.letArrow_whiskerRight, whiskerRight, Eqv.toEqv_toArr, Eqv.letT₂, Eqv.letT₂,
    Eqv.let₂_let₂, whiskerRight, Eqv.letArrow_comp
  ]
  congr 2
  conv => rhs; rw [Eqv.bind_pair_left]
  rw [Eqv.let₂_beta]
  conv => rhs; rw [Eqv.let_letArrow]
  congr 1
  rw [Eqv.bind_pair_left, Eqv.let_letArrow, Eqv.wk0_bv0]
  apply Eq.trans _ (Eqv.swap0_swap0 _)
  rw [Eqv.swap0, Eqv.swap0]
  induction g using Eqv.quotInd
  apply Eqv.of_tm
  simp [Wf.let₁, Wf.wk2, Wf.wk, Wf.wk1, Wf.pair, Wf.bv0, ren_ren, Wf.wk0, Ctx?.extend1, Wf.bv1]
  congr 1
  ext x; cases x <;> rfl

theorem DRWS.Arrow.comp_whiskerRight {A : R.Obj} (f : Arrow R B C) (g : Arrow R C D)
  : (f.comp g).whiskerRight A = (f.whiskerRight A).comp (g.whiskerRight A)
  := (f.whiskerRight_comp_whiskerRight g).symm

theorem Eqv.letArrow_tensorHom {A B A' B' : Ty α}
  (a : Eqv R Γ (A.tensor A')) (f : R.Arrow A B) (g : R.Arrow A' B')
  : a.letArrow (f.tensorHom g) = .letT₂ a (.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) (.letArrow .bv0 g)
  ) := by
  apply Eq.symm
  convert a.bind_let₂ _ _
  induction a, f, g using quotInd₃
  apply sound; apply Wf.eqv.of_tm;
  simp only [
    Wf.let₁, Wf.wk, Wf.let₂, Wf.pair, Wf.bv1, Wf.bv0, Wf.wk2, Ctx?.extend1, Ctx?.Wk.ix,
    Ctx?.Wk.drop_ix, Ctx?.length
  ]
  simp [Ctx?.nil, Ctx?.cons, Ctx?.erase, ren_ren, <-Nat.liftWk_comp]
  constructor <;> rfl

def DRWS.Arrow.ltimes {A B A' B' : Ty α} (f : Arrow R A A') (g : Arrow R B B')
  : Arrow R (A.tensor B) (A'.tensor B') := (f.whiskerRight _).comp (g.whiskerLeft _)

theorem DRWS.Arrow.tensorHom_eq_ltimes {A B A' B' : Ty α} (f : Arrow R A A') (g : Arrow R B B')
  : f.tensorHom g = f.ltimes g := by
  rw [
    ltimes, comp, Eqv.letArrow_whiskerLeft, whiskerRight, Eqv.toEqv_toArr, Eqv.letT₂_letT₂,
    Eqv.letT₂_beta, tensorHom
  ]
  congr 2
  rw [Eqv.bind_pair_left]
  congr 1
  apply Eq.symm
  induction g using Eqv.quotInd with
  | h hg =>
  apply Eqv.sound
  apply Wf.eqv.coh_out
  apply Wf.pre_beta_pureIIn
  simp
  simp [
    Wf.subst, Wf.pair, Wf.bv0, Wf.wk0, Wf.let₁, Wf.wk2, Wf.wk, Wf.bv1, SubstDS.refl_get, ren_ren,
  ]
  rw [<-subst_renIn, <-subst_ofRen]
  apply Subst.subst_eqOn_fvi
  intro x hx
  cases x
  rfl
  have hg := hg.deriv.fvi_le_length
  simp at hg
  omega

def DRWS.Arrow.rtimes {A B A' B' : Ty α} (f : Arrow R A A') (g : Arrow R B B')
  : Arrow R (A.tensor B) (A'.tensor B') := (g.whiskerLeft _).comp (f.whiskerRight _)

def DRWS.Arrow.tensorHomLeft {A B C A' B' C'}
  (f : Arrow R A A') (g : Arrow R B B') (h : Arrow R C C')
  : Arrow R ((A.tensor B).tensor C) ((A'.tensor B').tensor C')
  := Eqv.toArr (.letT₂ .bv0 (.let₂ (Ctx?.erase_left _).right.left .bv1 (
    .pair (Ctx?.erase_left _).left.left
    (.pair (Ctx?.erase_right _).right (.letArrow .bv1 f) (.letArrow .bv0 g)) (.letArrow .bv2 h)
  )))

def DRWS.Arrow.tensorHomRight  {A B C A' B' C'}
  (f : Arrow R A A') (g : Arrow R B B') (h : Arrow R C C')
  : Arrow R (A.tensor (B.tensor C)) (A'.tensor (B'.tensor C'))
  := Eqv.toArr (.letT₂ .bv0 (.let₂ (Ctx?.erase_right _).right .bv0 (
    .pair (Ctx?.erase_right _).right.right (.letArrow .bv3 f)
      (.pair (Ctx?.erase_right _).right (.letArrow .bv1 g) (.letArrow .bv0 h))
  )))

def DRWS.Arrow.rtensorHom (f : Arrow R A A') (g : Arrow R B B')
  : Arrow R (A.tensor B) (A'.tensor B') := Eqv.toArr (.letT₂ .bv0 (.antipair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) (.letArrow .bv0 g)
  ))

theorem DRWS.Arrow.tensorHom_left  {A B C A' B' C'}
  (f : Arrow R A A') (g : Arrow R B B') (h : Arrow R C C')
  : (f.tensorHom g).tensorHom h = f.tensorHomLeft g h
  := by
  rw [tensorHom, tensorHomLeft]
  congr 2
  rw [Eqv.bind_pair_left, Eqv.letArrow_tensorHom, Eqv.letT₂, Eqv.let_let₂]
  apply Eqv.let₂_coh'
  rfl
  conv => rhs; rw [Eqv.bind_pair_left]
  induction f, g, h using Eqv.quotInd₃
  apply Eqv.of_tm
  simp [Wf.let₁, Wf.pair, Wf.wk1, Wf.bv0, Wf.wk0, Wf.bv2, Wf.wk, ren_ren]
  congr
  ext x; cases x <;> rfl

theorem DRWS.Arrow.tensorHom_right {A B C A' B' C'}
  (f : Arrow R A A') (g : Arrow R B B') (h : Arrow R C C')
  : f.tensorHom (g.tensorHom h) = f.tensorHomRight g h
  := by
  rw [tensorHom, tensorHomRight]
  congr 2

  sorry

def DRWS.Arrow.tensorHomSwap0 (f : Arrow R A A') (g : Arrow R B B')
  : Arrow R (A.tensor B) (A'.tensor B')
  := Eqv.toArr (.letT₂ (.reswap .bv0) (Eqv.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) (.letArrow .bv0 g)
  ).swap0)

theorem DRWS.Arrow.tensorHom_eq_swap0 (f : Arrow R A A') (g : Arrow R B B')
  : f.tensorHom g = f.tensorHomSwap0 g
  := by
  rw [tensorHom, tensorHomSwap0, Eqv.letT₂, Eqv.letT₂, Eqv.let₂_reswap, Eqv.swap0_swap0]
  rfl

def DRWS.Arrow.tensorHomReswap (f : Arrow R A A') (g : Arrow R B B')
  : Arrow R (A.tensor B) (A'.tensor B')
  := Eqv.toArr (.letT₂ (.reswap .bv0) (.pair
    (((Ctx?.erase_left _).cons (.right _)).cons (.left _))
     (.letArrow .bv0 f) (.letArrow .bv1 g)
  ))

-- theorem DRWS.Arrow.tensorHom_eq_reswap (f : Arrow R A B) (g : Arrow R A' B')
--   : f.tensorHom g = f.tensorHomReswap g
--   := sorry
