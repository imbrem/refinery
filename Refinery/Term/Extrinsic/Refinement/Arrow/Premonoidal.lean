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

theorem DRWS.Arrow.whiskerLeft_comp_whiskerLeft {A : R.Obj}
  (f : Arrow R B C) (g : Arrow R C D)
  : (f.whiskerLeft A).comp (g.whiskerLeft A) = (f.comp g).whiskerLeft A
  := by
  rw [comp, Eqv.letArrow_whiskerLeft, whiskerLeft, Eqv.toEqv_toArr, Eqv.let₂_let₂, whiskerLeft]
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

def Eqv.releft {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (.tensor .unit A)) : Eqv R Γ A
  := .let₂ (Ctx?.erase_left _) a .bv0

def Eqv.releft_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : Eqv R Γ (.tensor .unit A)
  := .pair (Ctx?.erase_left _) (.unit _) a

-- theorem Eqv.releft_inv_releft {Γ : Ctx? α} {A : Ty α}
--   (a : Eqv R Γ A) : a.releft_inv.releft = a := by
--   rw [releft_inv, releft, let₂_beta]
--   conv => rhs; rw [<-let₁_eta a]
--   sorry

-- theorem Eqv.releft_releft_inv {Γ : Ctx? α} {A : Ty α}
--   (a : Eqv R Γ (.tensor .unit A)) : a.releft.releft_inv = a
--   := sorry

def DRWS.Obj.leftUnitor (A : R.Obj) : Arrow R (.tensor .unit A) A
  := Eqv.toArr (Eqv.bv0.releft)

def DRWS.Obj.leftUnitor_inv (A : R.Obj) : Arrow R A (.tensor .unit A)
  := Eqv.toArr (Eqv.bv0.releft_inv)

def Eqv.reright {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (A.tensor .unit)) : Eqv R Γ A
  := .let₂ (Ctx?.erase_left _) a .bv1

def Eqv.reright_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : Eqv R Γ (A.tensor .unit)
  := .pair (Ctx?.erase_right _) a (.unit _)

def DRWS.Obj.rightUnitor (A : R.Obj) : Arrow R (A.tensor .unit) A
  := Eqv.toArr (Eqv.bv0.reright)

def DRWS.Obj.rightUnitor_inv (A : R.Obj) : Arrow R A (A.tensor .unit)
  := Eqv.toArr (Eqv.bv0.reright_inv)

def Eqv.reassoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : Eqv R Γ (A.tensor (B.tensor C))
  := .let₂ (Ctx?.erase_left _) a (
    .let₂ ((Ctx?.erase_left _).cons (.left _)) .bv1 (.pair
      ((((Ctx?.erase_left _).cons (.right _)).cons (.left _)).cons (.right _))
      .bv1
      (.pair
        ((((Ctx?.erase_left _).cons (.right _)).cons (.left _)).cons (.left _))
        .bv0
        .bv2
      ))
  )

def Eqv.reassoc_inv {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : Eqv R Γ ((A.tensor B).tensor C)
  := .let₂ (Ctx?.erase_left _) a (
    .let₂ ((Ctx?.erase_right _).cons (.right _)) .bv0 (.pair
      ((Ctx?.erase_right _).cons (.right _))
      (.pair
        ((((Ctx?.erase_right _).cons (.right _)).cons (.right _)).cons (.left _))
        .bv3 .bv1)
      .bv0
    ))

def DRWS.Obj.assoc (A B C : R.Obj) : Arrow R ((A.tensor B).tensor C) (A.tensor (B.tensor C))
  := Eqv.toArr (.reassoc .bv0)

def DRWS.Obj.assoc_inv (A B C : R.Obj) : Arrow R (A.tensor (B.tensor C)) ((A.tensor B).tensor C)
  := Eqv.toArr (.reassoc_inv .bv0)

theorem Eqv.letArrow_assoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : a.letArrow (DRWS.Obj.assoc A B C) = a.reassoc
  := by
  rw [reassoc, bind_let₂]
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

theorem Eqv.let₂_reassoc {Γ Γl Γr : Ctx? α} {X Y A B C : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (X.tensor Y)) (b : Eqv R ((Γl.cons ⟨X, ⊤⟩).cons ⟨Y, ⊤⟩) ((A.tensor B).tensor C))
  : (a.let₂ hΓ b).reassoc = a.let₂ hΓ b.reassoc
  := by
  rw [reassoc, let₂_let₂]
  induction a, b using quotInd₂
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let₂_reassoc_inv {Γ Γl Γr : Ctx? α} {X Y A B C : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (X.tensor Y)) (b : Eqv R ((Γl.cons ⟨X, ⊤⟩).cons ⟨Y, ⊤⟩) (A.tensor (B.tensor C)))
  : (a.let₂ hΓ b).reassoc_inv = a.let₂ hΓ b.reassoc_inv
  := by
  rw [reassoc_inv, let₂_let₂]
  induction a, b using quotInd₂
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl

-- theorem Eqv.reassoc_beta {Γ Γc Γl Γm Γr : Ctx? α} {A B C : Ty α}
--   (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
--   (a : Eqv R Γl A) (b : Eqv R Γm B) (c : Eqv R Γr C)
--   : ((a.pair hΓc b).pair hΓ c).reassoc = a.pair (hΓ.s12_3_1_23 hΓc) (b.pair (hΓ.s12_3_23 hΓc) c)
--   := by
--   sorry

-- theorem Eqv.reassoc_reassoc_inv {Γ : Ctx? α} {A B C : Ty α}
--   (a : Eqv R Γ ((A.tensor B).tensor C))
--   : a.reassoc.reassoc_inv = a
--   := sorry
