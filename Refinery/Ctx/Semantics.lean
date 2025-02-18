import Refinery.Model
import Refinery.Ctx.Basic

import Discretion.Utils.Category

namespace Refinery

open CategoryTheory

open MonoidalCategory

open Monoidal

open EffectfulCategory

section TyModel

variable {α : Type _} [HasQuant α]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
         [TyModel α C]

notation "v⟦" v "⟧" => t⟦ Var?.ety v ⟧

abbrev Ctx?.den (Γ : Ctx? α ε) : C := t⟦Γ.ety⟧

notation "g⟦" Γ "⟧" => Ctx?.den Γ

end TyModel

section VarModel

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
         [VarModel α C]


abbrev Var?.del.den {v : Var? α ε} (h : v.del) : (v⟦ v ⟧ : C) ⟶ 𝟙_ C
  := !_ v.ety

abbrev Var?.copy.den {v : Var? α ε} (h : v.copy) : (v⟦ v ⟧ : C) ⟶ v⟦ v ⟧ ⊗ v⟦ v ⟧
  := Δ_ v.ety

def Var?.Wk.den {v w : Var? α ε} (h : v ≤ w) : (v⟦ v ⟧ : C) ⟶ v⟦ w ⟧
  := match v, w, h with
  | v, ⟨B, 0, _⟩, h => (h.unused_del rfl).den
  | ⟨A, (_ : Quant), _⟩, ⟨B, (_ : Quant), _⟩, h => eq_hom (by cases h.ty; rfl)

@[simp]
theorem Var?.Wk.den_zero {v : Var? α ε} {A : Ty α} {e : ε} (h : v ≤ ⟨A, 0, e⟩)
  : Var?.Wk.den (C := C) h = (h.unused_del rfl).den
  := by cases v with | mk _ q _ => cases q <;> rfl

@[simp]
theorem Var?.Wk.den_quant {v : Var? α ε} {A : Ty α} {q : Quant} {e : ε} (h : v ≤ ⟨A, q, e⟩)
  : Var?.Wk.den (C := C) h = eq_hom (by rw [ety_eq_quant h])
  := by cases v with | mk _ q' _ =>
        cases q' with | zero => have h := h.q; cases h using EQuant.le.casesLE | _ => rfl

def Ctx?.PWk.den {Γ Δ : Ctx? α ε} (h : Γ.PWk Δ) : (g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧
  := match Γ, Δ, h with
  | .nil, .nil, _ => 𝟙 (𝟙_ C)
  | .cons _ _, .cons _ _, h => h.tail.den ⊗ (Var?.Wk.den h.head)

@[simp]
def Ctx?.Wk.den {Γ Δ : Ctx? α ε} : Γ.Wk Δ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧)
  | .nil => 𝟙 (𝟙_ C)
  | .cons hΓ hv => hΓ.den ⊗ (Var?.Wk.den hv)
  | .skip hΓ hv => (hΓ.den ⊗ hv.den) ≫ (ρ_ _).hom

def Var.Ix.den {Γ : Ctx? α ε} {v : Var? α ε} (h : v.Ix Γ) : (g⟦ Γ ⟧ : C) ⟶ v⟦ v ⟧
  := Ctx?.Wk.den h ≫ (λ_ _).hom

def Ctx?.At.den {v : Var? α ε} {Γ : Ctx? α ε} {n} (h : Γ.At v n) : (g⟦ Γ ⟧ : C) ⟶ v⟦ v ⟧ :=
  h.inductionOn
    (λ _ d _ h => (d.den ⊗ (Var?.Wk.den h)) ≫ (λ_ _).hom)
    (λ _ _ _ _ hw p => (p ⊗ hw.den) ≫ (ρ_ _).hom)

@[simp]
theorem Ctx?.At.den_zero {v w : Var? α ε} {Γ : Ctx? α ε} (h : (Γ.cons w).At v 0)
  : h.den (C := C)
  = (h.zero_cons_tail.den (C := C) ⊗ (Var?.Wk.den h.zero_cons_head)) ≫ (λ_ _).hom
  := rfl

@[simp]
theorem Ctx?.At.den_succ {v w : Var? α ε} {Γ : Ctx? α ε} (h : (Γ.cons w).At v (n + 1))
  : h.den (C := C)
  = (h.succ_cons_tail.den (C := C) ⊗ h.succ_cons_head.den) ≫ (ρ_ _).hom
  := rfl

def Var?.PSSplit.den {u v w : Var? α ε} : u.PSSplit v w → ((v⟦ u ⟧ : C) ⟶ v⟦ v ⟧ ⊗ v⟦ w ⟧)
  | .left _ _ _ => (ρ_ _).inv
  | .right _ _ _ => (λ_ _).inv
  | .sboth h => have _ := h.copy; Δ_ _

theorem Var?.Wk.den_eff_in {v : Var? α ε} {A : Ty α} {q} {e e' : ε}
  (h : v ≤ ⟨A, q, e⟩) (h' : v ≤ ⟨A, q, e'⟩)
  : Var?.Wk.den (C := C) h = Var?.Wk.den h'
  := by cases q using EQuant.casesZero <;> simp

theorem Ctx?.At.den_eff {A : Ty α} {q} {e e' : ε} {Γ : Ctx? α ε} {n}
  (hΓe : Γ.At ⟨A, q, e⟩ n) (hΓe' : Γ.At ⟨A, q, e'⟩ n)
  : hΓe.den (C := C) = hΓe'.den
  := by induction hΓe with
  | here =>
    cases hΓe'; simp only [den_zero, Iso.cancel_iso_hom_right]
    congr 1; apply Var?.Wk.den_eff_in
  | there _ _ _ _ _ I => cases hΓe'; simp [*]

variable [BraidedCategoryStruct C]

def Ctx?.PSSplit.den {Γ Δ Ξ : Ctx? α ε} : Γ.PSSplit Δ Ξ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧ ⊗ g⟦ Ξ ⟧)
  | .nil => (λ_ _).inv
  | .cons hΓ hv => (hΓ.den ⊗ hv.den) ≫ swap_inner _ _ _ _

end VarModel

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
         [BraidedCategoryStruct C] [Iterate C] [E : Elgot2 C ε]
         [M : Model φ α ε C]

@[simp]
theorem Var?.Wk.den_eff {A : Ty α} {q : EQuant} {e e' : ε} (h : ⟨A, q, e⟩ ≤ ⟨A, q, e'⟩)
  : Var?.Wk.den (C := C) h = 𝟙 _
  := by cases q using EQuant.casesZero with
    | zero => simp [Var?.del.den, ety]
    | rest q => rfl

@[simp]
theorem Var?.del.den_pure {v : Var? α ε} (h : v.del) : E.HasEff e h.den := inferInstance

@[simp]
theorem Var?.copy.den_pure {v : Var? α ε} (h : v.copy) : E.HasEff e h.den := inferInstance

@[simp]
instance Var?.Wk.den_pure {e : ε} {v w : Var? α ε} (h : v ≤ w)
  : E.HasEff e <| Var?.Wk.den h
  := by cases v with | mk _ qv _ => cases w with | mk _ qw _ => cases qw using EQuant.casesZero with
    | zero => rw [den_zero]; infer_instance
    | rest qw => rw [den_quant]; infer_instance

instance Var?.Wk.den_central {v w : Var? α ε} (h : v ≤ w)
  : Central (C := C) (Var?.Wk.den h)
  := (den_pure h).pure_central

@[simp]
theorem Var?.Wk.den_comp {u v w : Var? α ε} (h : u ≤ v) (h' : v ≤ w)
  : den h ≫ den h' = den (C := C) (le_trans h h')
  := by cases u with | mk _ qu _ => cases v with | mk _ qv _ => cases w with | mk _ qw _ =>
    cases qw using EQuant.casesZero with
    | zero =>
      simp [Var?.del.den]
      exact M.drop_aff (⊥ : ε) _ (hA := ety_aff_zero (le_trans h h')) (hB := ety_aff_zero h')
    | rest qw =>  cases qv using EQuant.casesZero with
    | zero => cases h'.q using EQuant.le.casesLE
    | rest qv => simp

@[simp]
theorem Var?.Wk.den_comp_drop {v w : Var? α ε} (h : v ≤ w) [hw : w.del]
  : Var?.Wk.den h ≫ !_ w.ety = (hw.anti h).den (C := C)
  := by rw [M.drop_aff ⊥ _ (hA := (hw.anti h).ety_aff)]

variable [IsPremonoidal C]

instance Ctx?.Wk.den_pure {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) : E.HasEff e h.den := by induction h with
  | nil => simp only [den]; exact HasEff.id
  | skip =>
    simp only [den]; apply HasEff.comp (hf := _) (hg := _); apply HasEff.tensorHom; infer_instance
  | cons => simp only [den]; infer_instance

instance Ctx?.Wk.den_central {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) : Central (C := C) h.den
  := (den_pure h).pure_central

@[reassoc]
theorem Ctx?.Wk.den_comp {Γ Δ Ξ : Ctx? α ε} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ)
  : h.den ≫ h'.den = (h.comp h').den (C := C)
  := by induction h generalizing Ξ with
  -- TODO: why is this not simping?
  | nil => cases h'; simp [den, Wk.comp]; apply Category.id_comp
  | skip _ _ I => simp [
      den, Wk.comp, <-Monoidal.rightUnitor_naturality, <-Monoidal.whiskerRight_comp_assoc, I,
      Monoidal.tensor_eq_rtimes_left, rtimes]
  | cons _ hv I => cases h' with
  | skip _ hw => simp [den, Wk.comp, <-Monoidal.tensor_comp_left_assoc, I]
  | cons => simp [den, Wk.comp, <-Monoidal.tensor_comp_left, I]

instance Ctx?.At.den_pure {v : Var? α ε} {Γ : Ctx? α ε} {n} (h : Γ.At v n)
  : E.HasEff e h.den
  := by induction h <;> simp <;> infer_instance

instance Ctx?.At.den_central {v : Var? α ε} {Γ : Ctx? α ε} {n} (h : Γ.At v n)
  : Central (C := C) h.den
  := (den_pure h).pure_central

@[simp]
theorem Ctx?.At.den_wkOut {v w : Var? α ε} {Γ : Ctx? α ε} {n} (hΓv : Γ.At v n) (hvw : v ≤ w)
  : hΓv.den (C := C) ≫ Var?.Wk.den hvw = (hΓv.wkOut hvw).den
  := by induction hΓv with
  | here =>
    simp only [Ctx?.den, ety, Ty.den, den_zero, Monoidal.tensorHom_def, Category.assoc, ←
      Monoidal.leftUnitor_naturality]
    rw [<-Monoidal.whiskerLeft_comp_assoc, Var?.Wk.den_comp]
    rfl
  | there _ _ _ _ _ I =>
    simp only [den_succ, Category.assoc, ← Monoidal.rightUnitor_naturality]
    rw [Monoidal.tensor_eq_rtimes_left, Monoidal.tensor_eq_rtimes_left]
    simp only [rtimes, Category.assoc]
    rw [<-Monoidal.whiskerRight_comp_assoc, I]

@[simp]
theorem Ctx?.At.den_wkIn {Γ Δ : Ctx? α ε} (w : Γ.Wk Δ) {v n} (hΔv : Δ.At v n)
  : w.den (C := C) ≫ hΔv.den = (hΔv.wkIn w).den := by induction w generalizing n with
  | nil => cases hΔv
  | skip => simp [
    <-Monoidal.rightUnitor_naturality, <-Monoidal.tensorHom_id,
    <-Monoidal.tensor_comp_left_assoc, *]
  | cons => cases hΔv with
  | here =>
    simp [<-Monoidal.tensor_comp_left_assoc, Wk.den_comp]
    congr
    apply wk_nil_unique
  | there => simp [<-Monoidal.tensor_comp_left_assoc, Wk.den_comp, *]

-- TODO: Ctx?.At.ix.den = Ctx?.At.den

-- TODO: Var?.Ix.at.den = Var?.Ix.den

-- TODO: PWk composition

-- TODO: den(PWk.toWk) = den(PWk)

-- TODO: PSSplit ; swap

-- TODO: PSSplit ==> PSSplit, PSSplit vs PSSplit?

-- TODO: Split? SSplit?
