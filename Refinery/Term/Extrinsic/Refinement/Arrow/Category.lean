import Refinery.Term.Extrinsic.Wf.Rewrite
import Refinery.Term.Extrinsic.Wf.PreBeta
import Mathlib.CategoryTheory.Category.Basic

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

def Eqv.toArr (a : Eqv R (.one ⟨A, ⊤⟩) B) : DRWS.Arrow R A B := a

def DRWS.idArr (R : DRWS φ α) (A : Ty α) : Arrow R A A := (PreArrow.refl R A).e

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

def Eqv.letArrow {Γ : Ctx? α} {A B : Ty α} (a : Eqv R Γ A) (b : R.Arrow A B) : Eqv R Γ B
  := a.let₁ Γ.erase_left (b.extend1 Γ.erase)

theorem Eqv.letArrow_mk {Γ : Ctx? α} {A B : Ty α} {a : Wf R Γ A} {b : R.PreArrow A B}
  : (e⟦a⟧).letArrow b.e = e⟦a.letArrow b⟧ := rfl

def DRWS.Arrow.comp {A B C : Ty α} (f : DRWS.Arrow R A B) (g : DRWS.Arrow R B C)
  : DRWS.Arrow R A C := (Eqv.letArrow f.toEqv g).toArr

theorem DRWS.Arrow.id_comp {A B : Ty α} (f : DRWS.Arrow R A B)
  : (DRWS.idArr R A).comp f = f := f.let₁_bv0

theorem DRWS.Arrow.comp_id {A B : Ty α} (f : DRWS.Arrow R A B)
  : f.comp (DRWS.idArr R B) = f := f.let₁_eta

theorem DRWS.Arrow.comp_assoc {A B C D : Ty α}
  (f : DRWS.Arrow R A B) (g : DRWS.Arrow R B C) (h : DRWS.Arrow R C D)
  : (f.comp g).comp h = f.comp (g.comp h) := by
  simp only [DRWS.Arrow.comp, Eqv.letArrow, Eqv.let_let₁, Eqv.toArr, toEqv]
  induction f, g, h using Eqv.quotInd₃
  apply Eqv.sound
  apply Wf.eqv.of_tm
  simp [Wf.wk, Wf.let₁, Wf.wk1, Ctx?.extend1, ren_ren, <-Nat.liftWk_comp]
  rfl

instance DRWS.arrowCat (R : DRWS φ α) [R.UWkCongr] : Category (DRWS.Obj R) where
  Hom := DRWS.Arrow R
  id := R.idArr
  comp := DRWS.Arrow.comp
  id_comp f := f.id_comp
  comp_id f := f.comp_id
  assoc f g h := f.comp_assoc g h

theorem DRWS.Obj.id_def (A : R.Obj) : 𝟙 A = R.idArr A := rfl

theorem DRWS.Arrow.comp_def {A B C : R.Obj} (f : A ⟶ B) (g : B ⟶ C) : f ≫ g = f.comp g := rfl

end Term

end Refinery
