import Refinery.Model
import Refinery.Ctx.Basic

import Discretion.Premonoidal.BraidedHelpers
import Discretion.Premonoidal.Category
import Discretion.Monoidal.CoherenceLemmas

namespace Refinery

open CategoryTheory

open PremonoidalCategory MonoidalCategory'

open scoped MonoidalCategory

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
         {C : Type _} [Category C] [ChosenFiniteCoproducts C]

section MonoidalCategoryStruct

variable [MonoidalCategoryStruct C] [VarModel α C]

abbrev Var?.del.den {v : Var? α ε} (h : v.del) : (v⟦ v ⟧ : C) ⟶ 𝟙_ C
  := !_ v.ety

abbrev Var?.copy.den {v : Var? α ε} (h : v.copy) : (v⟦ v ⟧ : C) ⟶ v⟦ v ⟧ ⊗ v⟦ v ⟧
  := Δ_ v.ety

def Var?.Wk.den {v w : Var? α ε} (h : v ≤ w) : (v⟦ v ⟧ : C) ⟶ v⟦ w ⟧
  := match v, w, h with
  | v, ⟨B, 0, _⟩, h => (h.unused_del rfl).den
  | ⟨A, (_ : Quant), _⟩, ⟨B, (_ : Quant), _⟩, h => eqToHom (by cases h.ty; rfl)

theorem Var?.Wk.den_zero {v : Var? α ε} {A : Ty α} {e : ε} (h : v ≤ ⟨A, 0, e⟩)
  : Var?.Wk.den (C := C) h = (h.unused_del rfl).den
  := by cases v with | mk _ q _ => cases q <;> rfl

@[simp]
theorem Var?.Wk.den_unused {v w : Var? α ε} (h : v ≤ w) (hw : w.unused)
  : Var?.Wk.den (C := C) h = ((Var?.unused.del hw).anti h).den ≫ eqToHom (by simp [ety, hw])
  := by cases w; cases hw; rw [den_zero]; simp

theorem Var?.Wk.den_erase {v  w: Var? α ε} (h : v ≤ w.erase)
  : Var?.Wk.den (C := C) h = (h.unused_del rfl).den
  := by simp

theorem Var?.Wk.den_quant {v : Var? α ε} {A : Ty α} {q : Quant} {e : ε} (h : v ≤ ⟨A, q, e⟩)
  : Var?.Wk.den (C := C) h = eqToHom (by rw [ety_eq_quant h])
  := by cases v with | mk _ q' _ =>
        cases q' with | zero => have h := h.q; cases h using EQuant.le.casesLE | _ => rfl

@[simp]
theorem Var?.Wk.den_used {v w : Var? α ε} (h : v ≤ w) (hw : w.used)
  : Var?.Wk.den (C := C) h = eqToHom (by rw [ety_eq_used h hw])
  := by cases w with | mk A q e => cases q using EQuant.casesZero with
    | zero => cases hw
    | rest q => rw [den_quant]

def Ctx?.PWk.den {Γ Δ : Ctx? α ε} (h : Γ.PWk Δ) : (g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧
  := match Γ, Δ, h with
  | .nil, .nil, _ => 𝟙 (𝟙_ C)
  | .cons _ _, .cons _ _, h => h.tail.den ⊗ (Var?.Wk.den h.head)

@[simp]
def Ctx?.Wk.den {Γ Δ : Ctx? α ε} : Γ.Wk Δ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧)
  | .nil => 𝟙 (𝟙_ C)
  | .cons hΓ hv => hΓ.den ⊗ (Var?.Wk.den hv)
  | .skip hΓ hv => (hΓ.den ⊗ hv.den) ≫ (ρ_ _).hom

notation "w⟦" ρ "⟧" => Ctx?.Wk.den ρ

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
  | .left _ => (ρ_ _).inv
  | .right _ => (λ_ _).inv
  | .sboth h => have _ := h.copy; Δ_ _

@[simp]
theorem Var?.PSSplit.den_left (v : Var? α ε) : (PSSplit.left v).den (C := C) = (ρ_ _).inv := rfl

@[simp]
theorem Var?.PSSplit.den_right (v : Var? α ε) : (PSSplit.right v).den (C := C) = (λ_ _).inv := rfl

@[simp]
theorem Var?.PSSplit.den_sboth {v : Var? α ε} (h : v.scopy)
  : (PSSplit.sboth h).den (C := C) = have _ := h.copy; Δ_ _ := rfl

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

end MonoidalCategoryStruct

section BraidedCategory

variable [PremonoidalCategory C] [BraidedCategory' C] [VarModel α C]

@[simp]
def Ctx?.PSSplit.den {Γ Δ Ξ : Ctx? α ε} : Γ.PSSplit Δ Ξ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧ ⊗ g⟦ Ξ ⟧)
  | .nil => (λ_ _).inv
  | .cons hΓ hv => (hΓ.den ⊗ hv.den) ≫ (βi_ _ _ _ _).hom

notation "ps⟦" ρ "⟧" => Ctx?.Wk.den ρ

end BraidedCategory

end VarModel

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [ChosenFiniteCoproducts C]
         [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε]
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

@[simp]
theorem Var?.del.den_unused {v : Var? α ε} (hv : v.unused)
  : hv.del.den (C := C) = eqToHom (by simp [ety, hv])
  := by cases v; cases hv; simp [den, M.drop_unit]

@[simp]
theorem Var?.Wk.den_from_unused {v w : Var? α ε} (h : v ≤ w) (h' : v.unused)
  : Var?.Wk.den (C := C) h
  = eqToHom (by cases v; cases w; cases h'; cases h.q using EQuant.le.casesLE; rfl)
  := by cases v; cases w; cases h'; cases h.q using EQuant.le.casesLE;
        simp [den_zero (C := C) h, M.drop_unit]

theorem Var?.Wk.den_from_zero {v : Var? α ε} {A : Ty α} {e : ε} (h : ⟨A, 0, e⟩ ≤ v)
  : Var?.Wk.den (C := C) h = eqToHom (by cases v; cases h.q using EQuant.le.casesLE; rfl)
  := by simp

theorem Var?.Wk.den_from_erase {v w : Var? α ε} (h : v.erase ≤ w)
  : Var?.Wk.den (C := C) h = eqToHom (by cases v; cases w; cases h.q using EQuant.le.casesLE; rfl)
  := by simp

@[simp]
instance Var?.PSSplit.den_pure {u v w : Var? α ε} (h : u.PSSplit v w) : E.HasEff e h.den
  := by cases h <;> simp; infer_instance

@[simp]
instance Var?.PSSplit.den_central {u v w : Var? α ε} (h : u.PSSplit v w) : Central (C := C) h.den
  := (den_pure h).pure_central

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
  | skip _ _ I => simp only [
      den, Wk.comp, <-rightUnitor_naturality, <-comp_whiskerRight_assoc, I,
      tensorHom_def, Central.left_exchange, Category.assoc]
  | cons _ hv I => cases h' with
  | skip _ hw => simp [den, Wk.comp, <-tensor_comp_of_left_assoc, I]
  | cons => simp [den, Wk.comp, <-tensor_comp_of_left, I]

instance Ctx?.At.den_pure {v : Var? α ε} {Γ : Ctx? α ε} {n} (h : Γ.At v n)
  : E.HasEff e h.den
  := by induction h <;> simp <;> infer_instance

instance Ctx?.At.den_central {v : Var? α ε} {Γ : Ctx? α ε} {n} (h : Γ.At v n)
  : Central (C := C) h.den
  := (den_pure h).pure_central

@[simp]
instance Ctx?.PSSplit.den_pure {Γ Δ Ξ : Ctx? α ε} (h : Γ.PSSplit Δ Ξ) : E.HasEff e h.den
  := by induction h <;> simp; infer_instance

@[simp]
instance Ctx?.PSSplit.den_central {Γ Δ Ξ : Ctx? α ε} (h : Γ.PSSplit Δ Ξ) : Central (C := C) h.den
  := (den_pure h).pure_central

@[simp]
theorem Ctx?.At.den_wkOut {v w : Var? α ε} {Γ : Ctx? α ε} {n} (hΓv : Γ.At v n) (hvw : v ≤ w)
  : hΓv.den (C := C) ≫ Var?.Wk.den hvw = (hΓv.wkOut hvw).den
  := by induction hΓv with
  | here =>
    simp only [Ctx?.den, ety, Ty.den, den_zero, tensorHom_def, Category.assoc, ←
      leftUnitor_naturality]
    rw [<-PremonoidalCategory.whiskerLeft_comp_assoc, Var?.Wk.den_comp]
    rfl
  | there _ _ _ _ _ I =>
    simp only [den_succ, Category.assoc, ← rightUnitor_naturality]
    rw [tensorHom_def_of_left, tensorHom_def_of_left]
    simp only [Category.assoc]
    rw [<-comp_whiskerRight_assoc, I]

@[simp]
theorem Ctx?.At.den_wkIn {Γ Δ : Ctx? α ε} (w : Γ.Wk Δ) {v n} (hΔv : Δ.At v n)
  : w.den (C := C) ≫ hΔv.den = (hΔv.wkIn w).den := by induction w generalizing n with
  | nil => cases hΔv
  | skip => simp [
    <-PremonoidalCategory.rightUnitor_naturality, <-tensorHom_id,
    <-tensor_comp_of_left_assoc, *]
  | cons => cases hΔv with
  | here =>
    simp [<-tensor_comp_of_left_assoc, Wk.den_comp]
    congr
    apply wk_nil_unique
  | there => simp [<-tensor_comp_of_left_assoc, Wk.den_comp, *]

theorem Var?.PSSplit.wk_den {u' u v w : Var? α ε} (ρ : u' ≤ u) (σ : u.PSSplit v w)
  : Var?.Wk.den ρ ≫ σ.den (C := C)
  = (σ.wk ρ).den ≫ (Var?.Wk.den (C := C) (σ.leftWk ρ) ⊗ Var?.Wk.den (σ.rightWk ρ))
  := by cases u with | mk A q e => cases q using EQuant.casesZero with
  | zero => cases σ with
    | sboth h => cases h.q using EQuant.le.casesLE
    | right =>
      simp only [
        ety_quant_zero, leftUnitor_inv_naturality, rightUnitor_inv_naturality,
        id_tensorHom, wk, Wk.den_zero, den_right
      ]
      simp
    | left =>
      apply (cancel_mono (f := (ρ_ (𝟙_ C)).hom)).mp
      simp [ety_quant_zero, id_tensorHom, unitors_inv_equal]
  | rest => cases σ with
    | sboth h =>
      simp [den, wkLeft_sboth, wkRight_sboth]
      rw [
        Model.copy_rel_ltimes ⊥ _ (hA := (h.anti ρ).copy.ety_rel) (hB := h.copy.ety_rel),
        tensorHom_def
      ]
    | _ =>
      simp only [
        leftUnitor_inv_naturality, rightUnitor_inv_naturality,
        tensorHom_id, id_tensorHom, Wk.den_quant, den_left, den_right
      ]
      simp

local notation "PW" => Ctx?.PSSplit.wk

local notation "LW" => Ctx?.PSSplit.leftWk

local notation "RW" => Ctx?.PSSplit.rightWk

local notation "WR" => Ctx?.PSSplit.wkRight

local notation "WL" => Ctx?.PSSplit.wkLeft

-- theorem Ctx.PSSplit.wk_den {Γ' Γ Δ Ξ : Ctx? α ε} (ρ : Γ'.Wk Γ) (σ : Γ.PSSplit Δ Ξ)
--   : ρ.den ≫ σ.den (C := C) = (σ.wk ρ).den ≫ ((σ.leftWk ρ).den (C := C) ⊗ (σ.rightWk ρ).den)
--   := by induction ρ generalizing Δ Ξ with
--   | nil =>
--     cases σ
--     calc
--     _ = 𝟙 (𝟙_ C) ≫ (λ_ (𝟙_ C)).inv := rfl
--     _ = (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ 𝟙 (𝟙_ C)) := by simp
--     _ = _ := rfl
--   | skip ρ hv I =>
--     calc
--     _ = (ρ.den (C := C) ⊗ hv.den) ≫ (ρ_ _).hom ≫ σ.den := by simp
--     _ = _ ◁ hv.den ≫ (ρ_ _).hom ≫ ρ.den (C := C) ≫ σ.den
--       := by simp only [tensor_eq_rtimes_left, Category.assoc, Monoidal.rightUnitor_naturality_assoc]
--     _ = _ ◁ hv.den ≫ (ρ_ _).hom ≫ (σ.wk ρ).den ≫ ((σ.leftWk ρ).den (C := C) ⊗ (σ.rightWk ρ).den)
--       := by simp [I]
--     _ = ((σ.wk ρ).den (C := C) ⊗ hv.den) ≫ (ρ_ _).hom
--           ≫ ((σ.leftWk ρ).den (C := C) ⊗ (σ.rightWk ρ).den)
--       := by simp only [tensor_eq_rtimes_left, Category.assoc, Monoidal.rightUnitor_naturality_assoc]
--     _ = _ := by sorry
--     -- simp [
--     --   Monoidal.tensor_eq_rtimes_left, Category.assoc, Monoidal.rightUnitor_naturality_assoc,
--     --   Monoidal.rightUnitor_naturality, I]
--   | cons => sorry

-- TODO: Ctx?.At.ix.den = Ctx?.At.den

-- TODO: Var?.Ix.at.den = Var?.Ix.den

-- TODO: PWk composition

-- TODO: den(PWk.toWk) = den(PWk)

-- TODO: PSSplit ; swap

-- TODO: PSSplit ==> PSSplit, PSSplit vs PSSplit?

-- TODO: Split? SSplit?
