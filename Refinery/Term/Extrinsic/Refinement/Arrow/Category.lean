import Refinery.Term.Extrinsic.Wf.Rewrite
import Refinery.Term.Extrinsic.Wf.PreBeta
import Refinery.Term.Extrinsic.Wf.LetThen
import Discretion.Poset2.Basic

open HasQuant HasPQuant HasCommRel

open CategoryTheory

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

set_option linter.unusedVariables false in
def DRWS.Obj (R : DRWS φ α) := Ty α

def DRWS.PreArrow (R : DRWS φ α) (A B : Ty α) : Type _ := Wf R (.one ⟨A, ⊤⟩) B

instance DRWS.PreArrow.instPreorder
  (R : DRWS φ α) (A B : Ty α) : Preorder (DRWS.PreArrow R A B)
  := Wf.instPreorder R _ _

instance DRWS.PreArrow.setoid (R : DRWS φ α) (A B : Ty α) : Setoid (DRWS.PreArrow R A B)
  := Wf.setoid R _ _

def DRWS.Arrow (R : DRWS φ α) (A B : Ty α) : Type _ := Eqv R (.one ⟨A, ⊤⟩) B

instance DRWS.Arrow.instPartialOrder
  (R : DRWS φ α) (A B : Ty α) : PartialOrder (DRWS.Arrow R A B)
  := Eqv.instPartialOrder R _ _

variable {R : DRWS φ α}

def DRWS.PreArrow.toWf (a : DRWS.PreArrow R A B) : Wf R (.one ⟨A, ⊤⟩) B := a

def DRWS.PreArrow.extend1 (Γ : Ctx? α) [hΓ : Γ.del] (a : DRWS.PreArrow R A B)
  : Wf R (Γ.cons ⟨A, ⊤⟩) B := a.toWf.wk (Γ.extend1 ⟨A, ⊤⟩)

def DRWS.PreArrow.e (a : DRWS.PreArrow R A B) : Arrow R A B := e⟦a⟧

def DRWS.PreArrow.refl (R : DRWS φ α) (A : Ty α) : PreArrow R A A := Wf.bv0

def Wf.letArrow {Γ : Ctx? α} {A B : Ty α} (a : Wf R Γ A) (b : R.PreArrow A B) : Wf R Γ B
  := a.let₁ Γ.erase_left (b.extend1 Γ.erase)

def DRWS.PreArrow.comp {A B C : Ty α} (f : DRWS.PreArrow R A B) (g : DRWS.PreArrow R B C)
  : DRWS.PreArrow R A C := Wf.letArrow f g

def DRWS.Arrow.toEqv (a : DRWS.Arrow R A B) : Eqv R (.one ⟨A, ⊤⟩) B := a

instance DRWS.Arrow.toEqv_effect {a : DRWS.Arrow R A B} [ha : a.HasEff e] : (a.toEqv).HasEff e
  := ha

def Eqv.toArr (a : Eqv R (.one ⟨A, ⊤⟩) B) : DRWS.Arrow R A B := a

instance Eqv.toArr_effect {a : Eqv R (.one ⟨A, ⊤⟩) B} [ha : a.HasEff e] : (a.toArr).HasEff e
  := ha

@[simp] theorem DRWS.Arrow.toArr_toEqv {a : DRWS.Arrow R A B} : a.toEqv.toArr = a := rfl

@[simp] theorem Eqv.toEqv_toArr {a : Eqv R (.one ⟨A, ⊤⟩) B} : a.toArr.toEqv = a := rfl

def DRWS.Obj.id (A : R.Obj) : Arrow R A A := (PreArrow.refl R A).e

theorem DRWS.PreArrow.le_sound {A B : Ty α} {a b : DRWS.PreArrow R A B} (h : a ≤ b) : a.e ≤ b.e
  := h

theorem DRWS.PreArrow.le_exact {A B : Ty α} {a b : DRWS.PreArrow R A B} (h : a.e ≤ b.e) : a ≤ b
  := h

theorem DRWS.PreArrow.sound {A B : Ty α} {a b : DRWS.PreArrow R A B} (h : a ≈ b) : a.e = b.e
  := Eqv.sound h

theorem DRWS.PreArrow.exact {A B : Ty α} {a b : DRWS.PreArrow R A B} (h : a.e = b.e) : a ≈ b
  := Eqv.exact h

variable [R.UWkCongr]

theorem Wf.rby.letArrow_congr {Γ : Ctx? α} {A B : Ty α} {a a' : Wf R Γ A} {b b' : R.PreArrow A B}
  (ha : a.rby a') (hb : b ≤ b') : (a.letArrow b).rby (a'.letArrow b')
  := ha.let₁_congr Γ.erase_left (hb.wk_congr (Γ.erase.extend1 ⟨A, ⊤⟩))

theorem DRWS.PreArrow.comp_le_congr {A B C : Ty α}
  {f f' : DRWS.PreArrow R A B} {g g' : DRWS.PreArrow R B C}
  (hf : f ≤ f') (hg : g ≤ g') : f.comp g ≤ f'.comp g'
  := Wf.rby.letArrow_congr hf hg

theorem Wf.equiv_letArrow_congr {Γ : Ctx? α} {A B : Ty α} {a a' : Wf R Γ A} {b b' : R.PreArrow A B}
  (ha : a ≈ a') (hb : b ≈ b') : (a.letArrow b) ≈ (a'.letArrow b')
  := ⟨ha.left.letArrow_congr hb.left, ha.right.letArrow_congr hb.right⟩

theorem DRWS.PreArrow.comp_congr {A B C : Ty α}
  {f f' : DRWS.PreArrow R A B} {g g' : DRWS.PreArrow R B C}
  (hf : f ≈ f') (hg : g ≈ g') : f.comp g ≈ f'.comp g'
  := Wf.equiv_letArrow_congr hf hg

def DRWS.Arrow.extend1 (Γ : Ctx? α) [hΓ : Γ.del] (a : DRWS.Arrow R A B)
  : Eqv R (Γ.cons ⟨A, ⊤⟩) B := a.toEqv.wk (Γ.extend1 ⟨A, ⊤⟩)

instance DRWS.Arrow.extend1_effect {Γ : Ctx? α} [hΓ : Γ.del] {a : DRWS.Arrow R A B}
  [ha : a.HasEff e] : (a.extend1 Γ).HasEff e
  := by rw [extend1]; infer_instance

def Eqv.letArrow {Γ : Ctx? α} {A B : Ty α} (a : Eqv R Γ A) (b : R.Arrow A B) : Eqv R Γ B
  := a.letT₁ (b.extend1 Γ.erase)

theorem Eqv.letArrow_mk {Γ : Ctx? α} {A B : Ty α} {a : Wf R Γ A} {b : R.PreArrow A B}
  : (e⟦a⟧).letArrow b.e = e⟦a.letArrow b⟧ := rfl

theorem Eqv.letArrow_id (a : Eqv R Γ A) : a.letArrow (DRWS.Obj.id A) = a
  := a.let₁_eta

instance Eqv.letArrow_effect {Γ : Ctx? α} {A B : Ty α} (a : Eqv R Γ A) (b : R.Arrow A B)
  [ha : a.HasEff e] [hb : b.HasEff e] : (a.letArrow b).HasEff e
  := by rw [letArrow, letT₁]; infer_instance

theorem Eqv.wk_letArrow {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) (a : Eqv R Δ A) (b : R.Arrow A B)
  : (a.letArrow b).wk ρ = (a.wk ρ).letArrow b := by
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  simp [Wf.wk, Wf.let₁, Ctx?.extend1, Ctx?.Wk.drop_ix, ren_ren, <-Nat.liftWk_comp]
  congr
  funext x; cases x; rfl
  simp only [Nat.liftWk_succ, Function.comp_apply, add_left_inj, Ctx?.Wk.ix_add_len]

theorem Eqv.wk0_letArrow (a : Eqv R Γ A) (b : R.Arrow A B) (x : Var? α) [hx : x.del]
  : (a.letArrow b).wk0 x = (a.wk0 x).letArrow b
  := by
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  simp [Wf.wk0, Wf.wk, Wf.let₁, Ctx?.extend1, Ctx?.Wk.drop_ix, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem Eqv.wk1_letArrow {Γ : Ctx? α} {v}
  (a : Eqv R (Γ.cons v) A) (b : R.Arrow A B) (x : Var? α) [hx : x.del]
  : (a.letArrow b).wk1 x = (a.wk1 x).letArrow b
  := by
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  simp [Wf.wk1, Wf.wk, Wf.let₁, Ctx?.extend1, Ctx?.Wk.drop_ix, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem Eqv.wk2_letArrow {Γ : Ctx? α} {l r}
  (a : Eqv R ((Γ.cons l).cons r) A) (b : R.Arrow A B) (x : Var? α) [hx : x.del]
  : (a.letArrow b).wk2 x = (a.wk2 x).letArrow b
  := by
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  simp [Wf.wk2, Wf.wk, Wf.let₁, Ctx?.extend1, Ctx?.Wk.drop_ix, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem DRWS.Arrow.bv0_letArrow (f : Arrow R A B) : Eqv.letArrow .bv0 f = f
  := f.let₁_bv0

theorem DRWS.Arrow.bv0_letArrow' (Γ : Ctx? α) [hΓ : Γ.del] (f : Arrow R A B)
  : Eqv.letArrow .bv0 f = f.extend1 Γ
  := by
  conv => rhs; rw [<-f.bv0_letArrow]
  induction f using Eqv.quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  simp [Wf.let₁, Wf.wk, Wf.bv0, Ctx?.extend1, ren_ren, <-Nat.liftWk_comp, Ctx?.Wk.drop_ix]
  rfl

theorem Eqv.bind_letArrow  {Γ : Ctx? α} {A B : Ty α} (a : Eqv R Γ A) (b : R.Arrow A B)
  : a.letArrow b = a.let₁ Γ.erase_left (.letArrow .bv0 b)
  := by rw [letArrow, letT₁, DRWS.Arrow.bv0_letArrow']

def DRWS.Arrow.comp {A B C : Ty α} (f : DRWS.Arrow R A B) (g : DRWS.Arrow R B C)
  : DRWS.Arrow R A C := (Eqv.letArrow f.toEqv g).toArr

instance DRWS.Arrow.comp_effect {A B C : Ty α} (f : DRWS.Arrow R A B) (g : DRWS.Arrow R B C)
  [hf : f.HasEff e] [hg : g.HasEff e] : (f.comp g).HasEff e
  := by rw [comp]; infer_instance

theorem DRWS.Arrow.id_comp {A B : Ty α} (f : DRWS.Arrow R A B)
  : (Obj.id A).comp f = f := f.let₁_bv0

theorem DRWS.Arrow.comp_id {A B : Ty α} (f : DRWS.Arrow R A B)
  : f.comp (Obj.id B) = f := f.let₁_eta

theorem DRWS.Arrow.comp_le_congr {A B C : Ty α}
  {f f' : DRWS.Arrow R A B} {g g' : DRWS.Arrow R B C}
  (hf : f ≤ f') (hg : g ≤ g') : f.comp g ≤ f'.comp g'
  := by induction f, g, f', g' using Eqv.quotInd₄; apply Wf.rby.letArrow_congr hf hg

theorem Eqv.let_letArrow
  {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr A) (f : DRWS.Arrow R A B) (b : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
  : (a.letArrow f).let₁ hΓ b
  = a.let₁ hΓ ((f.extend1 _).let₁ (Γl.erase_right.cons (.right _)) (b.wk1 _))
  := by
  rw [letArrow, letT₁, let_let₁]
  induction a, b, f using Eqv.quotInd₃
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [
    Wf.wk, Wf.let₁, Wf.wk1, Ctx?.extend1, ren_ren, <-Nat.liftWk_comp, Nat.stepWk, Ctx?.Wk.drop_ix,
    <-hΓ.left_length, <-hΓ.right_length
  ]

theorem Eqv.letArrow_let₁
  {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B) (f : DRWS.Arrow R B C)
  : (a.let₁ hΓ b).letArrow f = a.let₁ hΓ (b.letArrow f)
  := by
  rw [letArrow, letT₁, let_let₁]
  induction a, b, f using Eqv.quotInd₃
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [
    Wf.wk, Wf.let₁, Wf.wk1, Ctx?.extend1, ren_ren, <-Nat.liftWk_comp, Nat.stepWk, Ctx?.Wk.drop_ix,
    hΓ.left_length
  ]

theorem Eqv.letArrow_let₂
  {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (f : DRWS.Arrow R C D)
  : (a.let₂ hΓ b).letArrow f = a.let₂ hΓ (b.letArrow f)
  := by
  rw [letArrow, letT₁, let_let₂]
  induction a, b, f using Eqv.quotInd₃
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [
    Wf.wk, Wf.let₁, Wf.wk1, Ctx?.extend1, ren_ren, <-Nat.liftWk_comp, Nat.stepWk, Ctx?.Wk.drop_ix,
    hΓ.left_length, Wf.let₂
  ]

theorem Eqv.letArrow_letArrow (a : Eqv R Γr A) (f : DRWS.Arrow R A B) (g : DRWS.Arrow R B C)
  : (a.letArrow f).letArrow g = a.letArrow (f.comp g)
:= by
  simp only [letArrow, letT₁, let_let₁, DRWS.Arrow.comp]
  induction a, f, g using Eqv.quotInd₃
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [Wf.wk, Wf.let₁, Wf.wk1, Ctx?.extend1, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem Eqv.letArrow_comp (a : Eqv R Γr A) (f : DRWS.Arrow R A B) (g : DRWS.Arrow R B C)
  : a.letArrow (f.comp g) = (a.letArrow f).letArrow g := (a.letArrow_letArrow f g).symm

theorem DRWS.Arrow.comp_assoc {A B C D : Ty α}
  (f : DRWS.Arrow R A B) (g : DRWS.Arrow R B C) (h : DRWS.Arrow R C D)
  : (f.comp g).comp h = f.comp (g.comp h) := f.letArrow_letArrow g h

instance DRWS.arrowCat (R : DRWS φ α) [R.UWkCongr] : Category (DRWS.Obj R) where
  Hom := DRWS.Arrow R
  id := Obj.id
  comp := DRWS.Arrow.comp
  id_comp f := f.id_comp
  comp_id f := f.comp_id
  assoc f g h := f.comp_assoc g h

theorem DRWS.Obj.id_def (A : R.Obj) : 𝟙 A = A.id := rfl

theorem DRWS.Arrow.comp_def {A B C : R.Obj} (f : A ⟶ B) (g : B ⟶ C) : f ≫ g = f.comp g := rfl

instance DRWS.arrowRefines (R : DRWS φ α) [R.UWkCongr] : Refines (DRWS.Obj R) where
  refines f g := f.rby g

instance DRWS.arrowPos2 (R : DRWS φ α) [R.UWkCongr] : Poset2 (DRWS.Obj R) where
  refines_comp := Arrow.comp_le_congr
  refines_is_partial_order := {
    refl := le_refl (α := DRWS.Arrow _ _ _)
    trans _ _ _ := le_trans (α := DRWS.Arrow _ _ _)
    antisymm _ _ := le_antisymm (α := DRWS.Arrow _ _ _)
  }

end Term

end Refinery
