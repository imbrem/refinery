import Refinery.Model
import Refinery.Ctx.Basic
import Refinery.Ctx.SSplit

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

abbrev Ctx?.den (Γ : Ctx? α) : C := t⟦Γ.ety⟧

notation "g⟦" Γ "⟧" => Ctx?.den Γ

end TyModel

section VarModel


variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [ChosenFiniteCoproducts C]

section MonoidalCategoryStruct

variable [MonoidalCategoryStruct C] [VM : VarModel α C]

def Var?.Wk.den {v w : Var? α} (h : v.Wk w) : (v⟦ v ⟧ : C) ⟶ v⟦ w ⟧
  := match v, w, h with
  | v, ⟨B, 0⟩, h => haveI _ := (h.unused_del rfl); !_ _
  | ⟨A, (_ : Quant)⟩, ⟨B, (_ : Quant)⟩, h => eqToHom (by cases h.ty; rfl)

abbrev Var?.del.den {v : Var? α} (h : v.del) : (v⟦ v ⟧ : C) ⟶ 𝟙_ _ := !_ _

theorem Var?.Wk.den_zero {v : Var? α} {A : Ty α} (h : v.Wk ⟨A, 0⟩)
  : Var?.Wk.den (C := C) h = (haveI _ := (h.unused_del rfl); !_ _)
  := by cases v with | mk _ q => cases q <;> rfl

@[simp]
theorem Var?.Wk.den_unused {v w : Var? α} (h : v.Wk w) (hw : w.unused)
  : Var?.Wk.den (C := C) h
  = (haveI _ := (Var?.unused.del hw).anti h; !_ _) ≫ eqToHom (by simp [ety, hw])
  := by cases w; cases hw; rw [den_zero]; simp

theorem Var?.Wk.den_erase {v  w: Var? α} (h : v ≤ w.erase)
  : Var?.Wk.den (C := C) h = (haveI _ := h.unused_del rfl; !_ _)
  := by simp

theorem Var?.Wk.den_quant {v : Var? α} {A : Ty α} {q : Quant} (h : v.Wk ⟨A, q⟩)
  : Var?.Wk.den (C := C) h = eqToHom (by rw [ety_eq_quant h])
  := by cases v with | mk _ q' =>
        cases q' with | zero => have h := h.q; cases h using EQuant.le.casesLE | _ => rfl

@[simp]
theorem Var?.Wk.den_used {v w : Var? α} (h : v.Wk w) (hw : w.used)
  : Var?.Wk.den (C := C) h = eqToHom (by rw [ety_eq_used h hw])
  := by cases w with | mk A q => cases q using EQuant.casesZero with
    | zero => cases hw
    | rest q => rw [den_quant]

notation "vw⟦" ρ "⟧" => Var?.Wk.den ρ

@[simp]
def Ctx?.PWk.den {Γ Δ : Ctx? α} : Γ.PWk Δ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧)
  | .nil => 𝟙 (𝟙_ C)
  | .cons ρ w => ρ.den ⊗ (Var?.Wk.den w)

notation "pw⟦" ρ "⟧" => Ctx?.PWk.den ρ

@[simp]
def Ctx?.Wk.den {Γ Δ : Ctx? α} : Γ.Wk Δ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧)
  | .nil => 𝟙 (𝟙_ C)
  | .cons ρ hvw => ρ.den ⊗ vw⟦ hvw ⟧
  | .skip hΓ hv => (hΓ.den ⊗ !_ _) ≫ (ρ_ _).hom

notation "w⟦" ρ "⟧" => Ctx?.Wk.den ρ

def Var.Ix.den {Γ : Ctx? α} {v : Var? α} (h : v.Ix Γ) : (g⟦ Γ ⟧ : C) ⟶ v⟦ v ⟧
  := Ctx?.Wk.den h ≫ (λ_ _).hom

@[simp]
def Ctx?.At.den {v : Var? α} {Γ : Ctx? α} {n} : Γ.At v n → ((g⟦ Γ ⟧ : C) ⟶ v⟦ v ⟧)
  | .here _ h => (!_ _ ⊗ (Var?.Wk.den h)) ≫ (λ_ _).hom
  | .there x hw => (x.den ⊗ !_ _) ≫ (ρ_ _).hom

@[simp]
theorem Ctx?.At.den_cast {v v' : Var? α} {Γ Γ' : Ctx? α} {n n'} (x : Γ.At v n)
  (hΓ : Γ = Γ') (hv : v = v') (hn : n = n')
  : (x.cast hΓ hv hn).den (C := C) = eqToHom (by rw [hΓ]) ≫ x.den ≫ eqToHom (by rw [hv])
  := by cases hΓ; cases hv; cases hn; simp

theorem Ctx?.At.den_cast_src {v : Var? α} {Γ Γ' : Ctx? α} {n} (x : Γ.At v n)
  (hΓ : Γ = Γ') : (x.cast_src hΓ).den (C := C) = eqToHom (by rw [hΓ]) ≫ x.den
  := by simp

theorem Ctx?.At.den_cast_trg {v v' : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n) (hv : v = v')
  : (x.cast_trg hv).den (C := C) = x.den ≫ eqToHom (by rw [hv])
  := by simp

theorem Ctx?.At.den_cast_idx {v : Var? α} {Γ : Ctx? α} {n n'} (x : Γ.At v n) (hn : n = n')
  : (x.cast_idx hn).den (C := C) = x.den := by simp

-- @[simp]
-- theorem Ctx?.At.den_zero {v w : Var? α} {Γ : Ctx? α} (h : (Γ.cons w).At v 0)
--   : h.den (C := C)
--   = (h.zero_cons_tail.den (C := C) ⊗ (Var?.Wk.den h.zero_cons_head)) ≫ (λ_ _).hom
--   := by cases h; rfl

-- @[simp]
-- theorem Ctx?.At.den_succ {v w : Var? α} {Γ : Ctx? α} (h : (Γ.cons w).At v (n + 1))
--   : h.den (C := C)
--   = (h.succ_cons_tail.den (C := C) ⊗ h.succ_cons_head.den) ≫ (ρ_ _).hom
--   := by cases h; rfl

def Var?.Split.den {u v w : Var? α} : u.Split v w → ((v⟦ u ⟧ : C) ⟶ v⟦ v ⟧ ⊗ v⟦ w ⟧)
  | .neither _ => !_ _ ≫ (ρ_ _).inv
  | .left h => vw⟦h⟧ ≫ (ρ_ _).inv
  | .right h => vw⟦h⟧ ≫ (λ_ _).inv
  | .sboth hu hv hw => (haveI _ := hu.copy; Δ_ _) ≫ (vw⟦hv⟧ ⊗ vw⟦hw⟧)

@[simp]
theorem Var?.Split.den_neither {v : Var? α} [hv : v.del]
  : (Split.neither hv).den (C := C) = !_ _ ≫ (ρ_ _).inv := rfl

@[simp]
theorem Var?.Split.den_left {v w : Var? α} (h : v ≤ w)
  : (Split.left h).den (C := C) = vw⟦h⟧ ≫ (ρ_ _).inv := rfl

@[simp]
theorem Var?.Split.den_right {v w : Var? α} (h : v ≤ w)
  : (Split.right h).den (C := C) = vw⟦h⟧ ≫ (λ_ _).inv := rfl

@[simp]
theorem Var?.Split.den_sboth {u v w : Var? α} (hu : u.scopy) (hv : u ≤ v) (hw : u ≤ w)
  : (Split.sboth hu hv hw).den (C := C) = (have _ := hu.copy; Δ_ _) ≫ (hv.den (C := C) ⊗ vw⟦hw⟧)
  := rfl

notation "vs⟦" ρ "⟧" => Var?.Split.den ρ

def Var?.SSplit.den {u v w : Var? α} : u.SSplit v w → ((v⟦ u ⟧ : C) ⟶ v⟦ v ⟧ ⊗ v⟦ w ⟧)
  | .left _ => (ρ_ _).inv
  | .right _ => (λ_ _).inv
  | .sboth h => have _ := h.copy; Δ_ _

notation "vss⟦" ρ "⟧" => Var?.SSplit.den ρ

@[simp]
theorem Var?.SSplit.den_left (v : Var? α) : (SSplit.left v).den (C := C) = (ρ_ _).inv := rfl

@[simp]
theorem Var?.SSplit.den_right (v : Var? α) : (SSplit.right v).den (C := C) = (λ_ _).inv := rfl

@[simp]
theorem Var?.SSplit.den_sboth {v : Var? α} (h : v.scopy)
  : (SSplit.sboth h).den (C := C) = have _ := h.copy; Δ_ _ := rfl

theorem Var?.Wk.den_eff_in {v : Var? α} {A : Ty α} {q}
  (h : v ≤ ⟨A, q⟩) (h' : v ≤ ⟨A, q⟩)
  : Var?.Wk.den (C := C) h = Var?.Wk.den h'
  := by cases q using EQuant.casesZero <;> simp

end MonoidalCategoryStruct

section BraidedCategory

variable [PremonoidalCategory C] [BraidedCategory' C] [VarModel α C]

@[simp]
def Ctx?.Split.den {Γ Δ Ξ : Ctx? α} : Γ.Split Δ Ξ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧ ⊗ g⟦ Ξ ⟧)
  | .nil => (λ_ _).inv
  | .cons σ hlr => (σ.den ⊗ hlr.den) ≫ (βi_ _ _ _ _).hom

notation "cs⟦" ρ "⟧" => Ctx?.SSplit.den ρ

@[simp]
def Ctx?.SSplit.den {Γ Δ Ξ : Ctx? α} : Γ.SSplit Δ Ξ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧ ⊗ g⟦ Ξ ⟧)
  | .nil => (λ_ _).inv
  | .cons σ hlr => (σ.den ⊗ hlr.den) ≫ (βi_ _ _ _ _).hom

notation "css⟦" ρ "⟧" => Ctx?.SSplit.den ρ

end BraidedCategory

end VarModel

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [ChosenFiniteCoproducts C]
         [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε]
         [M : Model φ α ε C]

@[simp]
theorem Var?.Wk.den_refl {v : Var? α} : Var?.Wk.den (C := C) (le_refl v) = 𝟙 _
  := by cases v with | mk _ q => cases q using EQuant.casesZero with
  | zero => apply M.drop_unit
  | rest => rfl

@[simp]
theorem Var?.del.den_pure {v : Var? α} (h : v.del) : E.HasEff e (!_ v.ety) := inferInstance

@[simp]
theorem Var?.copy.den_pure {v : Var? α} (h : v.copy) : E.HasEff e (Δ_ v.ety) := inferInstance

@[simp]
instance Var?.Wk.den_pure {e : ε} {v w : Var? α} (h : v ≤ w)
  : E.HasEff e <| Var?.Wk.den h
  := by cases v with | mk _ qv => cases w with | mk _ qw => cases qw using EQuant.casesZero with
    | zero => rw [den_zero]; infer_instance
    | rest qw => rw [den_quant]; infer_instance

instance Var?.Wk.den_central {v w : Var? α} (h : v ≤ w)
  : Central (C := C) (Var?.Wk.den h)
  := (den_pure h).pure_central

@[simp]
theorem Var?.Wk.den_comp {u v w : Var? α} (h : u ≤ v) (h' : v ≤ w)
  : den h ≫ den h' = den (C := C) (le_trans h h')
  := by cases u with | mk _ qu => cases v with | mk _ qv => cases w with | mk _ qw =>
    cases qw using EQuant.casesZero with
    | zero =>
      simp
      exact M.drop_aff (⊥ : ε) _ (hA := ety_aff_zero (le_trans h h')) (hB := ety_aff_zero h')
    | rest qw =>  cases qv using EQuant.casesZero with
    | zero => cases h'.q using EQuant.le.casesLE
    | rest qv => simp

@[simp]
theorem Var?.Wk.den_comp_drop {v w : Var? α} (h : v ≤ w) [hw : w.del]
  : Var?.Wk.den (C := C) h ≫ !_ w.ety = (haveI _ := hw.anti h; !_ v.ety)
  := by rw [M.drop_aff ⊥ _ (hA := (hw.anti h).ety_aff)]

@[simp]
theorem Var?.del.den_unused {v : Var? α} (hv : v.unused)
  : (haveI _  := hv.del; !_ v.ety) = eqToHom (C := C) (by simp [ety, hv])
  := by cases v; cases hv; simp [M.drop_unit]

@[simp]
theorem Var?.Wk.den_from_unused {v w : Var? α} (h : v ≤ w) (h' : v.unused)
  : Var?.Wk.den (C := C) h
  = eqToHom (by cases v; cases w; cases h'; cases h.q using EQuant.le.casesLE; rfl)
  := by cases v; cases w; cases h'; cases h.q using EQuant.le.casesLE;
        simp [den_zero (C := C) h, M.drop_unit]

theorem Var?.Wk.den_from_zero {v : Var? α} {A : Ty α} (h : ⟨A, 0⟩ ≤ v)
  : Var?.Wk.den (C := C) h = eqToHom (by cases v; cases h.q using EQuant.le.casesLE; rfl)
  := by simp

theorem Var?.Wk.den_from_erase {v w : Var? α} (h : v.erase ≤ w)
  : Var?.Wk.den (C := C) h = eqToHom (by cases v; cases w; cases h.q using EQuant.le.casesLE; rfl)
  := by simp

@[simp]
instance Var?.Split.den_pure {u v w : Var? α} (h : u.Split v w) : E.HasEff e h.den
  := by cases h <;> simp <;> infer_instance

@[simp]
instance Var?.Split.den_central {u v w : Var? α} (h : u.Split v w) : Central (C := C) h.den
  := (den_pure h).pure_central

@[simp]
instance Var?.SSplit.den_pure {u v w : Var? α} (h : u.SSplit v w) : E.HasEff e h.den
  := by cases h <;> simp; infer_instance

@[simp]
instance Var?.SSplit.den_central {u v w : Var? α} (h : u.SSplit v w) : Central (C := C) h.den
  := (den_pure h).pure_central

instance Ctx?.PWk.den_pure {Γ Δ : Ctx? α} (h : Γ.PWk Δ) : E.HasEff e h.den
  := by induction h with
  | nil => simp only [den]; exact HasEff.id
  | cons => simp only [den]; infer_instance

instance Ctx?.PWk.den_central {Γ Δ : Ctx? α} (h : Γ.PWk Δ) : Central (C := C) h.den
  := (den_pure h).pure_central

instance Ctx?.Wk.den_pure {Γ Δ : Ctx? α} (h : Γ.Wk Δ) : E.HasEff e h.den := by induction h with
  | nil => simp only [den]; exact HasEff.id
  | skip =>
    simp only [den]; apply HasEff.comp (hf := _) (hg := _); apply HasEff.tensorHom; infer_instance
  | cons => simp only [den]; infer_instance

instance Ctx?.Wk.den_central {Γ Δ : Ctx? α} (h : Γ.Wk Δ) : Central (C := C) h.den
  := (den_pure h).pure_central

theorem Ctx?.PWk.den_toWk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ)
  : ρ.toWk.den = ρ.den (C := C) := by induction ρ <;> simp [*]

@[simp]
theorem Ctx?.Wk.den_refl {Γ : Ctx? α} : (Ctx?.Wk.refl Γ).den (C := C) = 𝟙 (g⟦ Γ ⟧) := by
  induction Γ <;> simp [*] <;> rfl

@[reassoc]
theorem Ctx?.Wk.den_comp {Γ Δ Ξ : Ctx? α} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ)
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

@[simp]
theorem Ctx?.Wk.den_comp_drop {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) [hΔ : Δ.del]
  : ρ.den (C := C) ≫ !_ Δ.ety = (haveI _ := hΔ.wk ρ; !_ Γ.ety)
  := have _ := hΔ.wk ρ; M.drop_aff ⊥ _

@[simp]
theorem Ctx?.PWk.den_refl {Γ : Ctx? α} : (refl Γ).den (C := C) = 𝟙 (g⟦ Γ ⟧) := by
  induction Γ <;> simp [*] <;> rfl

theorem Ctx?.PWk.den_single {Γ : Ctx? α} {v w : Var? α} (h : v ≤ w) :
  ((refl Γ).cons h).den (C := C) = _ ◁ h.den := by simp

theorem Ctx?.PWk.den_double {Γ : Ctx? α} {v w v' w': Var? α} (h : v ≤ w) (h' : v' ≤ w')
  : (((refl Γ).cons h).cons h').den (C := C) = (_ ◁ h.den) ▷ _ ≫ _ ◁ h'.den
    := by simp [tensorHom_def]

theorem Ctx?.PWk.den_comp {Γ Δ Ξ : Ctx? α} (ρ : Γ.PWk Δ) (ρ' : Δ.PWk Ξ)
  : ρ.den ≫ ρ'.den = (ρ.comp ρ').den (C := C)
  := by rw [<-ρ.den_toWk, <-ρ'.den_toWk, Wk.den_comp, <-PWk.comp_toWk, den_toWk]

instance Ctx?.At.den_pure {v : Var? α} {Γ : Ctx? α} {n} (h : Γ.At v n)
  : E.HasEff e h.den
  := by induction h <;> simp <;> infer_instance

instance Ctx?.At.den_central {v : Var? α} {Γ : Ctx? α} {n} (h : Γ.At v n)
  : Central (C := C) h.den
  := (den_pure h).pure_central

@[simp]
instance Ctx?.Split.den_pure {Γ Δ Ξ : Ctx? α} (h : Γ.Split Δ Ξ) : E.HasEff e h.den
  := by induction h <;> simp; infer_instance

@[simp]
instance Ctx?.SSplit.den_pure {Γ Δ Ξ : Ctx? α} (h : Γ.SSplit Δ Ξ) : E.HasEff e h.den
  := by induction h <;> simp; infer_instance

@[simp]
instance Ctx?.SSplit.den_central {Γ Δ Ξ : Ctx? α} (h : Γ.SSplit Δ Ξ) : Central (C := C) h.den
  := (den_pure h).pure_central

@[simp]
theorem Ctx?.At.den_wkOut {v w : Var? α} {Γ : Ctx? α} {n} (hΓv : Γ.At v n) (hvw : v ≤ w)
  : hΓv.den (C := C) ≫ Var?.Wk.den hvw = (hΓv.wkOut hvw).den
  := by induction hΓv with
  | here =>
    simp only [Ctx?.den, ety, Ty.den, tensorHom_def, Category.assoc, ←
      leftUnitor_naturality, Ctx?.At.den, Ctx?.At.wkOut]
    rw [<-PremonoidalCategory.whiskerLeft_comp_assoc, Var?.Wk.den_comp]
  | there _ _ I =>
    simp only [Ctx?.At.den, Ctx?.At.wkOut, Category.assoc, ← rightUnitor_naturality]
    rw [tensorHom_def_of_left, tensorHom_def_of_left]
    simp only [Category.assoc]
    rw [<-comp_whiskerRight_assoc, I]

@[simp]
theorem Ctx?.At.den_wkIn {Γ Δ : Ctx? α} (w : Γ.Wk Δ) {v n} (hΔv : Δ.At v n)
  : w.den (C := C) ≫ hΔv.den = (hΔv.wkIn w).den := by induction w generalizing n with
  | nil => cases hΔv
  | skip => simp [
    <-PremonoidalCategory.rightUnitor_naturality, <-tensorHom_id,
    <-tensor_comp_of_left_assoc, Ctx?.At.wkIn, *]
  | cons ρ _ => cases hΔv <;> simp [<-tensor_comp_of_left_assoc, Wk.den_comp, Ctx?.At.wkIn, *]

@[simp]
theorem Ctx?.At.den_pwk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {v n} (hΔv : Δ.At v n)
  : ρ.den (C := C) ≫ hΔv.den = (hΔv.pwk ρ).den
  := by rw [<-ρ.den_toWk, hΔv.den_wkIn, hΔv.wkIn_toWk]; simp

-- theorem Var?.Split.wk_den {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.Split v w)
--   : Var?.Wk.den ρ ≫ σ.den (C := C)
--   = (σ.wk ρ).den ≫ (Var?.Wk.den (C := C) (σ.leftWk ρ) ⊗ Var?.Wk.den (σ.rightWk ρ))
--   := by cases u with | mk A q => cases q using EQuant.casesZero with
--   | zero => cases σ with
--     | sboth h => cases h.q using EQuant.le.casesLE
--     | right =>
--       simp only [
--         ety_quant_zero, leftUnitor_inv_naturality, rightUnitor_inv_naturality,
--         id_tensorHom, wk, Wk.den_zero, den_right
--       ]
--       simp
--     | left =>
--       apply (cancel_mono (f := (ρ_ (𝟙_ C)).hom)).mp
--       simp [ety_quant_zero, id_tensorHom, unitors_inv_equal]
--   | rest => cases σ with
--     | sboth h =>
--       simp [den, wkLeft_sboth, wkRight_sboth]
--       rw [
--         Model.copy_rel_ltimes ⊥ _ (hA := (h.anti ρ).copy.ety_rel) (hB := h.copy.ety_rel),
--         tensorHom_def
--       ]
--     | _ =>
--       simp only [
--         leftUnitor_inv_naturality, rightUnitor_inv_naturality,
--         tensorHom_id, id_tensorHom, Wk.den_quant, den_left, den_right
--       ]
--       simp

-- TODO: Ctx?.At.ix.den = Ctx?.At.den

-- TODO: Var?.Ix.at.den = Var?.Ix.den

-- TODO: PWk composition

-- TODO: den(PWk.toWk) = den(PWk)

-- TODO: SSplit ; swap

-- TODO: SSplit ==> SSplit, SSplit vs SSplit?

-- TODO: Split? SSplit?
