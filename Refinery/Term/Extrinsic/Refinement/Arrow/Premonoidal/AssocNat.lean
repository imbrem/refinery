import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Binoidal
import Refinery.Term.Extrinsic.Wf.Let3

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

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
  rw [tensorHom, tensorHomRight, Eqv.letArrow_tensorHom, Eqv.letT₂]
  congr 2
  rw [Eqv.letT₂, Eqv.let₂_pair_left_pure]
  induction f, g, h using Eqv.quotInd₃
  apply Eqv.of_tm
  simp [Wf.bv0, Wf.let₂, Wf.pair, Wf.wk0, Wf.let₁, Wf.wk, ren_ren, Wf.bv1, Wf.bv3]
  congr
  ext x; cases x <;> rfl

theorem Eqv.letArrow_tensorHomRight {A B C A' B' C' : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  (f : DRWS.Arrow R A A') (g : DRWS.Arrow R B B') (h : DRWS.Arrow R C C')
  : a.letArrow (f.tensorHomRight g h)
  = .letT₂ a (.let₂ (Ctx?.erase_right _).right .bv0 (
    .pair (Ctx?.erase_right _).right.right (.letArrow .bv3 f)
      (.pair (Ctx?.erase_right _).right (.letArrow .bv1 g) (.letArrow .bv0 h))
  )) := by
  rw [letT₂, bind_let₂]
  induction a, f, g, h using quotInd₄ with
  | h a f g h =>
  apply of_tm
  simp only [
    Wf.let₁, Wf.wk, Wf.let₂, Wf.bv0, Wf.pair, Wf.bv3, Wf.wk2, Ctx?.extend1, Wf.bv1, ren, ren_ren
  ]
  simp
  constructorm* _ ∧ _ <;> {
    simp only [<-subst_ofRen]
    apply Subst.subst_eqOn_fvi
    intro x hx
    cases x <;> simp [Ctx?.Wk.drop_ix]
  }

theorem Eqv.letArrow_pure_tensorHomRight {A B C A' B' C' : Ty α} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γl A) (b : Eqv R Γm B) (c : Eqv R Γr C)
  [hb : b.HasEff ⊥] [hc : c.HasEff ⊥]
  (f : DRWS.Arrow R A A') (g : DRWS.Arrow R B B') (h : DRWS.Arrow R C C')
  : (a.pair hΓ (b.pair hΓc c)).letArrow (f.tensorHomRight g h)
  = .pair hΓ (a.letArrow f) (.pair hΓc (b.letArrow g) (c.letArrow h)) := by
  rw [letArrow_tensorHomRight, letT₂, let₂_beta]
  conv =>
    rhs; rw [bind_letArrow, let_pair_right]; rhs; rhs; rw [wk0_pair, wk0_letArrow, wk0_letArrow]
    rw [bind_letArrow]; arg 3; rw [bind_letArrow]
  rw [let_pure_pair_both, let₂_pair_left_pure]
  conv => rhs; rw [bind_let₂]
  induction a, b, c using quotInd₃
  induction f, g, h using quotInd₃
  apply of_tm
  simp only [
    Wf.let₁, Wf.wk0, Wf.let₂, Wf.pair, Wf.bv0, Wf.bv3, Wf.wk, Wf.bv1, Wf.wk2, Wf.wk1, ren, ren_ren
  ]
  simp
  constructorm* _ ∧ _ <;> {
    congr 1
    ext x; cases x
    <;> simp [
      Ctx?.extend1, Ctx?.Wk.drop_ix,
      <-hΓ.left_length, <-hΓ.right_length, <-hΓc.left_length, <-hΓc.right_length
    ]
  }

theorem DRWS.Arrow.tensorHomLeft_reassoc {A B C A' B' C'}
   (f : Arrow R A A') (g : Arrow R B B') (h : Arrow R C C')
  : (f.tensorHomLeft g h).toEqv.reassoc = Eqv.letArrow (.reassoc .bv0) (f.tensorHomRight g h)
  := by
  simp only [
    tensorHomLeft, Eqv.letT₂, Ctx?.erase_cons, Ctx?.erase_nil, Var?.erase_erase,
    Eqv.toEqv_toArr, Eqv.let₂_reassoc, Eqv.reassoc_beta, EQuant.coe_top, Var?.erase,
    Ctx?.erase_right, Ctx?.erase_left
  ]
  conv => rhs; rw [Eqv.reassoc, Eqv.letT₂, Eqv.letArrow, Eqv.letT₁, Eqv.let_let₂, Eqv.let_let₂]
  convert_to _ = (
    Eqv.let₂
    (Ctx?.erase_right _).right
    Eqv.bv0
    (Eqv.let₂
      (Ctx?.erase_right _).right.left
      Eqv.bv1
      (Eqv.let₁
        (Ctx?.erase_left _)
        (Eqv.pair
          (Ctx?.erase_left _).left.right
          Eqv.bv1
          (Eqv.pair
            (Ctx?.erase_left _).right.right.left
            Eqv.bv0 Eqv.bv2))
        (Eqv.wk1 ⟨B, 0⟩
          (Eqv.wk1 ⟨A, 0⟩
            (Eqv.wk1 ⟨C, 0⟩
              (Eqv.wk1 ⟨A.tensor B, 0⟩
                (extend1
                  (Ctx?.nil.cons { ty := (A.tensor B).tensor C, q := ⊤ }).erase
                  (f.tensorHomRight g h))))))))
  )
  induction f, g, h using Eqv.quotInd₃
  apply Eqv.of_tm
  simp [Wf.let₂, Wf.pair, Wf.let₁]
  congr 1
  apply Eqv.let₂_coh'
  rfl
  convert_to _ = (Eqv.letArrow (Eqv.pair
      (((Ctx?.nil.cons { ty := (A.tensor B).tensor C, q := 0 }).cons { ty := A.tensor B, q := 0 }).cons
              { ty := C, q := ⊤ }).erase_left.left.right
      Eqv.bv1
      (Eqv.pair
        ((Ctx?.nil.cons { ty := (A.tensor B).tensor C, q := 0 }).cons
                  { ty := A.tensor B, q := 0 }).erase_left.right.right.left
        Eqv.bv0 Eqv.bv2)) (f.tensorHomRight g h))
  · {
    induction f, g, h using Eqv.quotInd₃ with
    | h f g h =>
    apply Eqv.of_tm
    simp only [EQuant.coe_top, Wf.let₁, Ctx?.erase_cons, Ctx?.erase_nil, Var?.erase_erase, Wf.bv0,
      Wf.pair, Wf.let₂, Wf.wk1, let₁.injEq, true_and, Wf.wk, Wf.bv1, Wf.bv3]
    simp [Ctx?.extend1, ren_ren]
    constructorm* _ ∧ _ <;> {
      simp only [<-subst_ofRen]
      apply Subst.subst_eqOn_fvi
      intro x hx
      cases x <;> simp
    }
  }
  · {
    rw [Eqv.letArrow_pure_tensorHomRight]
    induction f, g, h using Eqv.quotInd₃
    apply Eqv.of_tm
    simp [Wf.pair]
  }

theorem DRWS.Arrow.associator_naturality {A B C A' B' C' : Obj R}
   (f : Arrow R A A') (g : Arrow R B B') (h : Arrow R C C')
  : ((f.tensorHom g).tensorHom h).comp (A'.assoc B' C')
  = (A.assoc B C).comp (f.tensorHom (g.tensorHom h)) := by
  rw [tensorHom_left, tensorHom_right, comp, Eqv.letArrow_assoc, tensorHomLeft_reassoc]; rfl

theorem DRWS.Obj.pentagon {A B C D : Obj R}
  : (((A.assoc B C).whiskerRight D).comp
    (A.assoc (B.tensor C) D)).comp
    ((B.assoc C D).whiskerLeft A)
  = (assoc (A.tensor B) C D).comp (A.assoc B (C.tensor D))
  := by
  rw [
    DRWS.Arrow.comp, DRWS.Arrow.comp, Eqv.toEqv_toArr, Eqv.letArrow_whiskerLeft
  ]
  sorry

--TODO: pentagon
