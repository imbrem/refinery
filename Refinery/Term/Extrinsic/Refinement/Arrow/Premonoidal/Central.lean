import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Binoidal

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def DRWS.Arrow.rtensorHom (f : Arrow R A A') (g : Arrow R B B')
  : Arrow R (A.tensor B) (A'.tensor B') := Eqv.toArr (.letT₂ .bv0 (.antipair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) (.letArrow .bv0 g)
  ))

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

theorem DRWS.Arrow.rtensorHom_eq_rtimes {A B A' B' : Ty α} (f : Arrow R A A') (g : Arrow R B B')
  : f.rtensorHom g = f.rtimes g := by
  rw [
    rtimes, comp, Eqv.letArrow_whiskerRight, whiskerLeft, Eqv.toEqv_toArr, Eqv.letT₂, Eqv.letT₂,
    Eqv.let₂_let₂, Eqv.let₂_beta, rtensorHom,
  ]
  congr 2
  rw [
    Eqv.antipair_def'
  ]
  conv => rhs; rhs; rhs; rw [Eqv.bind_pair_left]
  apply Eq.symm
  induction f, g using Eqv.quotInd₂ with
  | h f g =>
  apply Eqv.sound
  apply Wf.eqv.coh_out
  apply Wf.pre_beta_pureIIn
  simp
  simp [Wf.subst, Wf.let₁, Wf.bv0, Wf.wk, Wf.wk0, Wf.wk2, Wf.bv1, Wf.pair]
  constructorm* _ ∧ _
  · {
    simp [SubstDS.refl_get]
    intro h
    reduce at h
    cases h
  }
  · simp [<-subst_renIn]
    simp [<-subst_ofRen]
    apply Subst.subst_eqOn_fvi
    intro x hx
    have hx : x < 1 := lt_of_lt_of_le hx g.deriv.fvi_le_length
    cases x with
    | zero => rfl
    | succ x => simp at hx
  · simp [ren_ren]
    simp [<-subst_renIn]
    simp [<-subst_ofRen]
    apply Subst.subst_eqOn_fvi
    intro x hx
    have hx : x < 1 := lt_of_lt_of_le hx f.deriv.fvi_le_length
    cases x with
    | zero => rfl
    | succ x => simp at hx

theorem DRWS.Arrow.ltimes_eq_rtimes {A B A' B' : Ty α} (f : Arrow R A A') (g : Arrow R B B')
  [hf : f.HasEff ea] [hg : g.HasEff eb] (he : ea ⇌ eb)
  : f.ltimes g = f.rtimes g
  := by
  rw [
    <-tensorHom_eq_ltimes, <-rtensorHom_eq_rtimes, rtensorHom, Eqv.antipair_comm _ _ _ he]
  rfl

theorem DRWS.Arrow.ltimes_eq_rtimes_left {A B A' B' : Ty α} (f : Arrow R A A') (g : Arrow R B B')
  [hf : f.HasEff ⊥] : f.ltimes g = f.rtimes g
  := ltimes_eq_rtimes f g (eb := ⊤) HasCommRel.commutes_bot_left

theorem DRWS.Arrow.ltimes_eq_rtimes_right {A B A' B' : Ty α} (f : Arrow R A A') (g : Arrow R B B')
  [hg : g.HasEff ⊥] : f.ltimes g = f.rtimes g
  := ltimes_eq_rtimes f g (ea := ⊤) HasCommRel.commutes_bot_right

open CategoryTheory

open PremonoidalCategory

instance DRWS.Arrow.pure_central {A B : R.Obj} (f : Arrow R A B) [hf : f.HasEff ⊥]
  : Central (C := R.Obj) f where
  left_exchange _ := ltimes_eq_rtimes_left _ _
  right_exchange _ := ltimes_eq_rtimes_right _ _

-- theorem DRWS.Arrow.tensorHom_eq_reswap (f : Arrow R A B) (g : Arrow R A' B')
--   : f.tensorHom g = f.tensorHomReswap g
--   := sorry
