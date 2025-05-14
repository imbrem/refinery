import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Binoidal
import Refinery.Term.Extrinsic.Wf.Let3

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

theorem DRWS.Arrow.leftUnitor_naturality {A B : R.Obj} (f : Arrow R A B)
  : (f.whiskerLeft Ty.unit).comp B.leftUnitor = A.leftUnitor.comp f := by
  rw [comp, Eqv.letArrow_leftUnitor]
  congr 1
  rw [
    Eqv.releft, whiskerLeft, Eqv.letT₂, Eqv.letT₂, Eqv.toEqv_toArr, Eqv.let₂_let₂, Eqv.let₂_beta,
    Eqv.wk2_bv0, Eqv.wk2_bv0, Eqv.wk0_letArrow, Eqv.wk0_bv0, DRWS.Obj.leftUnitor, Eqv.releft,
    Eqv.letT₂, Eqv.toEqv_toArr, Eqv.letArrow_let₂
  ]
  congr 1
  conv => rhs; rw [<-Eqv.let₁_eta (Eqv.letArrow _ _)]
  induction f using Eqv.quotInd with
  | h f =>
  apply Eqv.sound
  apply Wf.eqv.coh_out
  apply Wf.pre_beta_pureIIn
  simp
  simp [Wf.subst, Wf.let₁, Wf.bv0, Wf.bv1, Wf.wk, <-subst_renIn]
  constructor
  rfl
  simp [<-subst_ofRen]
  apply Subst.subst_eqOn_fvi
  intro x hx
  have hx : x < 1 := lt_of_lt_of_le hx f.deriv.fvi_le_length
  cases x with
  | zero => rfl
  | succ x => simp at hx

theorem DRWS.Arrow.rightUnitor_naturality {A B : R.Obj} (f : Arrow R A B)
  : (f.whiskerRight Ty.unit).comp B.rightUnitor = A.rightUnitor.comp f := by
  rw [comp, Eqv.letArrow_rightUnitor]
  congr 1
  rw [
    Eqv.reright, whiskerRight, Eqv.letT₂, Eqv.letT₂, Eqv.toEqv_toArr, Eqv.let₂_let₂,
    Eqv.let₂_beta, Eqv.wk2_bv1, Eqv.wk2_bv1,
  ]
  conv => lhs; rhs; rhs; rhs; rw[<-Eqv.wk0_bv0]
  rw [
    Eqv.let₁_pure_wk0, Eqv.pwk_bv0, Eqv.let₁_eta_pwk, DRWS.Obj.rightUnitor, Eqv.reright,
    Eqv.toEqv_toArr, Eqv.letT₂, Eqv.letArrow_let₂,
  ]
  induction f using Eqv.quotInd
  apply Eqv.of_tm
  rfl

theorem DRWS.Obj.triangle {A B : R.Obj}
  : (assoc A Ty.unit B).comp ((leftUnitor B).whiskerLeft A)
  = (rightUnitor A).whiskerRight B
  := by
  rw [
    Arrow.comp, Eqv.letArrow_whiskerLeft, assoc, Eqv.toEqv_toArr, Arrow.whiskerRight,
    Eqv.letArrow_rightUnitor, Eqv.letArrow_leftUnitor, Eqv.reassoc_letT₂
  ]
  congr 2
  conv => rhs; rhs; rw [<-Eqv.releft_inv_releft .bv0]
  rw [Eqv.reright, Eqv.letT₂, Eqv.let₂_pair_right]
  congr 1
  rw [Eqv.unit_pure_del .bv0]
  apply Eqv.sound
  apply Wf.eqv.coh_out
  apply Wf.pre_beta_pureIIn
  simp
  rfl
