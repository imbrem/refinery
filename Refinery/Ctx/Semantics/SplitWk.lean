import Refinery.Ctx.Semantics

namespace Refinery

open CategoryTheory

open PremonoidalCategory MonoidalCategory'

open scoped MonoidalCategory

open EffectfulCategory

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [ChosenFiniteCoproducts C]
         [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε]
         [M : Model φ α ε C]

section LeftBias

theorem Var?.SSplit.wk_den {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : Var?.Wk.den ρ ≫ σ.den (C := C)
  = (σ.wk ρ).den ≫ (Var?.Wk.den (C := C) (σ.leftWk ρ) ⊗ Var?.Wk.den (σ.rightWk ρ))
  := by cases u with | mk A q => cases q using EQuant.casesZero with
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

local notation "PW" => Ctx?.SSplit.wk

local notation "LW" => Ctx?.SSplit.leftWk

local notation "RW" => Ctx?.SSplit.rightWk

local notation "WR" => Ctx?.SSplit.wkRight

local notation "WL" => Ctx?.SSplit.wkLeft

set_option maxHeartbeats 10000000 in
theorem Ctx?.SSplit.wk_den {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : ρ.den ≫ σ.den (C := C) = (σ.wk ρ).den ≫ ((σ.leftWk ρ).den (C := C) ⊗ (σ.rightWk ρ).den)
  := by induction ρ generalizing Δ Ξ with
  | nil =>
    cases σ
    calc
    _ = 𝟙 (𝟙_ C) ≫ (λ_ (𝟙_ C)).inv := rfl
    _ = (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ 𝟙 (𝟙_ C)) := by simp
    _ = _ := rfl
  | skip ρ hv I =>
    rename_i v
    calc
    _ = (ρ.den (C := C) ⊗ hv.den) ≫ (ρ_ _).hom ≫ σ.den := by simp
    _ = _ ◁ hv.den ≫ (ρ_ _).hom ≫ ρ.den (C := C) ≫ σ.den
      := by simp only [tensorHom_def_of_left, Category.assoc, rightUnitor_naturality_assoc]
    _ = _ ◁ hv.den ≫ (ρ_ _).hom ≫ (σ.wk ρ).den ≫ ((LW ρ σ).den (C := C) ⊗ (RW ρ σ).den)
      := by simp [I]
    _ = ((σ.wk ρ).den (C := C) ⊗ hv.den) ≫ (ρ_ _).hom ≫ ((LW ρ σ).den (C := C) ⊗ (RW ρ σ).den)
      := by simp only [tensorHom_def_of_left, Category.assoc, rightUnitor_naturality_assoc]
    _ = ((σ.wk ρ).den (C := C) ⊗ hv.den)
      ≫ (((LW ρ σ).den (C := C) ⊗ (RW ρ σ).den) ▷ _)
      ≫ (ρ_ _).hom
      := by simp only [rightUnitor_naturality]
    _ = _
      := by
      simp only [<-tensorHom_def_assoc]
      simp only [<-tensorHom_id, <-tensor_comp_of_left_assoc, Category.comp_id]
    ((PW ρ σ).den (C := C) ≫ ((LW ρ σ).den (C := C) ⊗ w⟦RW ρ σ⟧)) ▷ _
      ≫ (_ ◁ hv.den)
      ≫ (ρ_ _).hom
      = _ := by simp only [
        tensorHom_def, Category.assoc, comp_whiskerRight, comp_whiskerRight_assoc]
    (PW ρ σ).den (C := C) ▷ _
      ≫ (((LW ρ σ).den (C := C) ⊗ w⟦RW ρ σ⟧) ⊗ hv.den)
      ≫ (ρ_ _).hom
      = _ := by simp only [<-associator_naturality_assoc]; congr; premonoidal_coherence
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom
      ≫ (w⟦LW ρ σ⟧ ⊗ (w⟦RW ρ σ⟧ ⊗ hv.den))
      ≫ (_ ◁ (ρ_ g⟦Ξ⟧).hom)
      = _ := by simp only [
        tensorHom_def, PremonoidalCategory.whiskerLeft_comp,
        PremonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom
      ≫ (w⟦LW ρ σ⟧ ⊗ ((w⟦RW ρ σ⟧ ⊗ hv.den)
      ≫ (ρ_ g⟦Ξ⟧).hom))
      = _ := by simp only [
        <-comp_whiskerRight_assoc, Category.assoc, Iso.inv_hom_id_assoc, tensorHom_def]
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom ≫ (ρ_ _).inv ▷ _
      ≫ (((ρ_ _).hom ≫ w⟦LW ρ σ⟧) ▷ _)
      ≫ (_ ◁ ((w⟦RW ρ σ⟧ ⊗ hv.den) ≫ (ρ_ g⟦Ξ⟧).hom))
      = _
      := by simp only [tensorHom_def]
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom ≫ (ρ_ _).inv ▷ _
      ≫ ((ρ_ _).hom ≫ w⟦LW ρ σ⟧ ⊗ (w⟦RW ρ σ⟧ ⊗ hv.den)
      ≫ (ρ_ g⟦Ξ⟧).hom)
      = _ := by rw [swap_inner_tensor_leftUnitor_assoc]
    ((PW ρ σ).den (C := C) ⊗ (λ_ _).inv)
      ≫ (βi_ g⟦WL ρ σ⟧ g⟦WR ρ σ⟧ (𝟙_ C) _).hom
      ≫ ((ρ_ _).hom ≫ w⟦LW ρ σ⟧ ⊗ (w⟦RW ρ σ⟧ ⊗ hv.den)
      ≫ (ρ_ g⟦Ξ⟧).hom)
      = _ := by simp
  | cons ρ hvw I => cases σ with
  | cons σ hlr =>
    calc
    _ = (ρ.den (C := C) ⊗ vw⟦hvw⟧) ≫ (css⟦σ⟧ ⊗ vss⟦hlr⟧) ≫ (βi_ _ _ _ _).hom := by simp
    _ = ((ρ.den (C := C) ≫ css⟦σ⟧) ⊗ (vw⟦hvw⟧ ≫ vss⟦hlr⟧)) ≫ (βi_ _ _ _ _).hom
      := by rw [<-tensor_comp_of_left_assoc]
    _ = (((PW ρ σ).den (C := C) ≫ (w⟦LW ρ σ⟧ ⊗ w⟦RW ρ σ⟧)) ⊗ (vw⟦hvw⟧ ≫ vss⟦hlr⟧))
      ≫ (βi_ _ _ _ _).hom := by rw [I]
    _ = _ := by rw [Var?.SSplit.wk_den, tensor_comp_of_left_assoc]
    ((PW ρ σ).den (C := C) ⊗ vss⟦hlr.wk hvw⟧)
      ≫ ((w⟦LW ρ σ⟧ ⊗ w⟦RW ρ σ⟧) ⊗ (vw⟦hlr.leftWk hvw⟧ ⊗ vw⟦hlr.rightWk hvw⟧))
      ≫ (βi_ _ _ _ _).hom
      = _ := by rw [swap_inner_naturality_tensor_middle]
    ((PW ρ σ).den (C := C) ⊗ vss⟦hlr.wk hvw⟧)
      ≫ (βi_ _ _ _ _).hom
      ≫ ((w⟦LW ρ σ⟧ ⊗ vw⟦hlr.leftWk hvw⟧) ⊗ (w⟦RW ρ σ⟧ ⊗ vw⟦hlr.rightWk hvw⟧))
      = _ := by simp only [Ctx?.SSplit.wkLeft.eq_3,
        Ctx?.SSplit.wkRight.eq_3, Ctx?.SSplit.wk, Ctx?.SSplit.den, Ctx?.SSplit.leftWk,
        Ctx?.Wk.den, Ctx?.SSplit.rightWk, Category.assoc]

theorem Ctx?.SSplit.wk_den_assoc {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  (f : (g⟦Δ⟧ ⊗ g⟦Ξ⟧ : C) ⟶ X)
  : ρ.den ≫ σ.den (C := C) ≫ f
  = (σ.wk ρ).den ≫ ((σ.leftWk ρ).den (C := C) ⊗ (σ.rightWk ρ).den) ≫ f
  := by rw [<-Category.assoc, Ctx?.SSplit.wk_den, Category.assoc]

end LeftBias

section RightBias

theorem Var?.SSplit.wk_den' {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : Var?.Wk.den ρ ≫ σ.den (C := C)
  = (σ.wk' ρ).den ≫ (Var?.Wk.den (C := C) (σ.leftWk' ρ) ⊗ Var?.Wk.den (σ.rightWk' ρ))
  := by cases u with | mk A q => cases q using EQuant.casesZero with
  | zero => cases σ with
    | sboth h => cases h.q using EQuant.le.casesLE
    | right =>
      simp only [
        ety_quant_zero, leftUnitor_inv_naturality, rightUnitor_inv_naturality,
        id_tensorHom, wk', Wk.den_zero, den_right
      ]
      simp [MonoidalCategory'.unitors_inv_equal]
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

local notation "PW" => Ctx?.SSplit.wk'

local notation "LW" => Ctx?.SSplit.leftWk'

local notation "RW" => Ctx?.SSplit.rightWk'

local notation "WR" => Ctx?.SSplit.wkRight'

local notation "WL" => Ctx?.SSplit.wkLeft'

set_option maxHeartbeats 10000000 in
theorem Ctx?.SSplit.wk_den' {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : ρ.den ≫ σ.den (C := C) = (σ.wk' ρ).den ≫ ((σ.leftWk' ρ).den (C := C) ⊗ (σ.rightWk' ρ).den)
  := by induction ρ generalizing Δ Ξ with
  | nil =>
    cases σ
    calc
    _ = 𝟙 (𝟙_ C) ≫ (λ_ (𝟙_ C)).inv := rfl
    _ = (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ 𝟙 (𝟙_ C)) := by simp
    _ = _ := rfl
  | skip ρ hv I =>
    rename_i v
    calc
    _ = (ρ.den (C := C) ⊗ hv.den) ≫ (ρ_ _).hom ≫ σ.den := by simp
    _ = _ ◁ hv.den ≫ (ρ_ _).hom ≫ ρ.den (C := C) ≫ σ.den
      := by simp only [tensorHom_def_of_left, Category.assoc, rightUnitor_naturality_assoc]
    _ = _ ◁ hv.den ≫ (ρ_ _).hom ≫ (σ.wk' ρ).den ≫ ((LW ρ σ).den (C := C) ⊗ (RW ρ σ).den)
      := by simp [I]
    _ = ((σ.wk' ρ).den (C := C) ⊗ hv.den) ≫ (ρ_ _).hom ≫ ((LW ρ σ).den (C := C) ⊗ (RW ρ σ).den)
      := by simp only [tensorHom_def_of_left, Category.assoc, rightUnitor_naturality_assoc]
    _ = ((σ.wk' ρ).den (C := C) ⊗ hv.den)
      ≫ (((LW ρ σ).den (C := C) ⊗ (RW ρ σ).den) ▷ _)
      ≫ (ρ_ _).hom
      := by simp only [rightUnitor_naturality]
    _ = _
      := by
      simp only [<-tensorHom_def_assoc]
      simp only [<-tensorHom_id, <-tensor_comp_of_left_assoc, Category.comp_id]
    ((PW ρ σ).den (C := C) ≫ ((LW ρ σ).den (C := C) ⊗ w⟦RW ρ σ⟧)) ▷ _
      ≫ (_ ◁ hv.den)
      ≫ (ρ_ _).hom
      = _ := by simp only [
        tensorHom_def, Category.assoc, comp_whiskerRight, comp_whiskerRight_assoc]
    (PW ρ σ).den (C := C) ▷ _
      ≫ (((LW ρ σ).den (C := C) ⊗ w⟦RW ρ σ⟧) ⊗ hv.den)
      ≫ (ρ_ _).hom
      = _ := by simp only [<-associator_naturality_assoc]; congr; premonoidal_coherence
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom
      ≫ (w⟦LW ρ σ⟧ ⊗ (w⟦RW ρ σ⟧ ⊗ hv.den))
      ≫ (_ ◁ (ρ_ g⟦Ξ⟧).hom)
      = _ := by simp only [
        tensorHom_def, PremonoidalCategory.whiskerLeft_comp,
        PremonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom
      ≫ (w⟦LW ρ σ⟧ ⊗ ((w⟦RW ρ σ⟧ ⊗ hv.den)
      ≫ (ρ_ g⟦Ξ⟧).hom))
      = _ := by simp only [
        <-comp_whiskerRight_assoc, Category.assoc, Iso.inv_hom_id_assoc, tensorHom_def]
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom ≫ (ρ_ _).inv ▷ _
      ≫ (((ρ_ _).hom ≫ w⟦LW ρ σ⟧) ▷ _)
      ≫ (_ ◁ ((w⟦RW ρ σ⟧ ⊗ hv.den) ≫ (ρ_ g⟦Ξ⟧).hom))
      = _
      := by simp only [tensorHom_def]
    (PW ρ σ).den (C := C) ▷ _ ≫ (α_ _ _ _).hom ≫ (ρ_ _).inv ▷ _
      ≫ ((ρ_ _).hom ≫ w⟦LW ρ σ⟧ ⊗ (w⟦RW ρ σ⟧ ⊗ hv.den)
      ≫ (ρ_ g⟦Ξ⟧).hom)
      = _ := by rw [swap_inner_tensor_leftUnitor_assoc]
    ((PW ρ σ).den (C := C) ⊗ (λ_ _).inv)
      ≫ (βi_ g⟦WL ρ σ⟧ g⟦WR ρ σ⟧ (𝟙_ C) _).hom
      ≫ ((ρ_ _).hom ≫ w⟦LW ρ σ⟧ ⊗ (w⟦RW ρ σ⟧ ⊗ hv.den)
      ≫ (ρ_ g⟦Ξ⟧).hom)
      = _ := by
        simp only [swap_inner_tensorUnit_right, Category.assoc, wkLeft'.eq_2,
          wkRight'.eq_2, wk', den, Ty.den, Var?.SSplit.den_left, leftWk', Wk.den, rightWk',
          Var?.del.den_unused, eqToHom_refl, tensorHom_id, Iso.inv_hom_id, Category.comp_id,
          tensorHom_def, PremonoidalCategory.comp_whiskerRight_assoc, Ctx?.den, Ctx?.ety,
          <-swap_inner_naturality_outer_left_assoc,
          <-swap_inner_naturality_right_assoc, Var?.del.den]
        conv =>
          enter [1, 2, 2, 2, 2, 2, 2, 2, 2]
          rw [Central.left_exchange_assoc]
        premonoidal
  | cons ρ hvw I => cases σ with
  | cons σ hlr =>
    calc
    _ = (ρ.den (C := C) ⊗ vw⟦hvw⟧) ≫ (css⟦σ⟧ ⊗ vss⟦hlr⟧) ≫ (βi_ _ _ _ _).hom := by simp
    _ = ((ρ.den (C := C) ≫ css⟦σ⟧) ⊗ (vw⟦hvw⟧ ≫ vss⟦hlr⟧)) ≫ (βi_ _ _ _ _).hom
      := by rw [<-tensor_comp_of_left_assoc]
    _ = (((PW ρ σ).den (C := C) ≫ (w⟦LW ρ σ⟧ ⊗ w⟦RW ρ σ⟧)) ⊗ (vw⟦hvw⟧ ≫ vss⟦hlr⟧))
      ≫ (βi_ _ _ _ _).hom := by rw [I]
    _ = _ := by rw [Var?.SSplit.wk_den', tensor_comp_of_left_assoc]
    ((PW ρ σ).den (C := C) ⊗ vss⟦hlr.wk' hvw⟧)
      ≫ ((w⟦LW ρ σ⟧ ⊗ w⟦RW ρ σ⟧) ⊗ (vw⟦hlr.leftWk' hvw⟧ ⊗ vw⟦hlr.rightWk' hvw⟧))
      ≫ (βi_ _ _ _ _).hom
      = _ := by rw [swap_inner_naturality_tensor_middle]
    ((PW ρ σ).den (C := C) ⊗ vss⟦hlr.wk' hvw⟧)
      ≫ (βi_ _ _ _ _).hom
      ≫ ((w⟦LW ρ σ⟧ ⊗ vw⟦hlr.leftWk' hvw⟧) ⊗ (w⟦RW ρ σ⟧ ⊗ vw⟦hlr.rightWk' hvw⟧))
      = _ := by simp only [Ctx?.SSplit.wkLeft.eq_3,
        Ctx?.SSplit.wkRight.eq_3, Ctx?.SSplit.wk', Ctx?.SSplit.den, Ctx?.SSplit.leftWk',
        Ctx?.Wk.den, Ctx?.SSplit.rightWk', Category.assoc]

theorem Ctx?.SSplit.wk_den'_assoc {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  (f : (g⟦Δ⟧ ⊗ g⟦Ξ⟧ : C) ⟶ X)
  : ρ.den ≫ σ.den (C := C) ≫ f
  = (σ.wk' ρ).den ≫ ((σ.leftWk' ρ).den (C := C) ⊗ (σ.rightWk' ρ).den) ≫ f
  := by rw [<-Category.assoc, Ctx?.SSplit.wk_den', Category.assoc]


end RightBias
