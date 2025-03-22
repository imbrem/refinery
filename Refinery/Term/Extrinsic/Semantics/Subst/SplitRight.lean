import Refinery.Term.Extrinsic.Semantics.Subst.Basic

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

theorem SubstDS.den_ssplit_pos' (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↠ (σ.ssplit hΔ).den' (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      ssplit, SubstSSplit.erase_left, SubstSSplit.den', den, <-tensorHom_def_of_right,
      Ctx?.SSplit.den_drop_tensor_left, Ctx?.PWk.den_refl'
    ]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hΔ with
  | cons hΔ hlr =>
  simp only [den, tensorHom_def, Category.assoc, Ctx?.SSplit.den]
  rw [<-Central.left_exchange_assoc, <-comp_whiskerRight_assoc]
  have Iσ' :
    css⟦hΓ⟧
    ≫ (σ.den (C := C) ≫ css⟦hΔ⟧) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    ↠ css⟦hΓ⟧
    ≫ (σ.ssplit hΔ).den' (C := C) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    := by apply refines_comp; rfl; apply refines_comp; apply refines_whiskerRight; apply Iσ; rfl
  apply refines_trans Iσ'
  cases hlr with
  | left =>
    apply refines_of_eq; apply Eq.symm
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_left,
      Category.assoc]
    split
    case isTrue h =>
      simp only [
        SubstSSplit.den', SubstDS.den, Deriv?.den_zero, Ctx?.SSplit.den_drop_tensor_right,
        Ctx?.PWk.den_refl', Category.id_comp, Ctx?.SSplit.den_comm, Category.assoc,
        <-braiding_naturality_left_assoc, <-braiding_naturality_right
      ]
      rw [
        PremonoidalCategory.whiskerLeft_comp_assoc, right_exchange_assoc,
        Ctx?.SSplit.den_s12_3_1_23_assoc
      ]
      congr 1
      simp only [
        comp_whiskerRight_assoc, Ctx?.SSplit.den_comm, <-associator_naturality_left_assoc,
        <-associator_naturality_middle_assoc, <-associator_naturality_right_assoc,
        Ctx?.den, Ctx?.ety, Ty.den, tensorHom_def, PremonoidalCategory.whiskerLeft_comp_assoc,
      ]
      congr 1
      simp only [
        <-comp_whiskerRight_assoc, <-braiding_naturality_right_assoc, <-braiding_naturality_left,
        PremonoidalCategory.whiskerLeft_comp_assoc,
      ]
      simp only [comp_whiskerRight_assoc, <-right_exchange_assoc, left_exchange_assoc]
      congr 3
      simp only [
        braiding_tensor_left, braiding_tensorUnit_left', braiding_tensor_right,
        braiding_tensorUnit_right'
      ]
      calc
      _ = ((β'_ _ _).hom ≫ (β'_ _ _).hom) ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (β'_ _ _).hom
        ≫ (α_ _ _ _).inv
        ≫ _ ◁ (ρ_ _).inv := by premonoidal
      _ = _ := by simp only [symmetry, swap_inner, assoc_inner]; premonoidal
    case isFalse h => cases v using Var?.casesZero with
    | zero =>
      simp only [
        SubstSSplit.den', den, tensorHom_def, Ty.den, Deriv?.unused, Deriv?.den_zero',
        right_exchange (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, Ctx?.den, Ctx?.ety, swap_inner_tensorUnit_right, Category.assoc
      ]
      simp only [
        PremonoidalCategory.whiskerLeft_comp_assoc, comp_whiskerRight_assoc, comp_whiskerRight
      ]
      rw [Ctx?.SSplit.den_s12_3_1_23_assoc, <-right_exchange_assoc, <-right_exchange]
      premonoidal
    | rest => simp at h
  | right =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
      Category.assoc, swap_inner_tensorUnit_right, SubstSSplit.den', Deriv?.den_zero,
      tensorHom_def_of_right, Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
      Category.id_comp, tensor_comp_of_right, PremonoidalCategory.whiskerLeft_comp_assoc,
      Category.assoc, Ctx?.den, Ctx?.ety
    ]
    rw [
      Ctx?.SSplit.den_s12_3_1_23_assoc, tensorHom_def,
      PremonoidalCategory.whiskerLeft_comp_assoc,
      <-swap_whiskerLeft_of_swap (g := da.den)
    ]
    premonoidal
    rw [<-E.eff_comm_exchange hcomm]
  | sboth hv =>
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_sboth,
      Category.assoc]
    split
    case isTrue hv' =>
      have hv : v.copy := hv.copy
      have hΓ : Γr.copy := da.copy hv' hv
      simp only [
        SubstSSplit.den', den, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      ]
      rw [
        <-left_exchange_assoc, <-tensorHom_def_of_right_assoc, Ctx?.SSplit.den_s12_34_13_24_assoc,
        tensorHom_def_assoc
      ]
      apply refines_comp; rfl
      apply refines_comp; rfl
      simp only [
        tensorHom_def, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
        Iso.inv_hom_id_assoc, Ctx?.den, Ty.den, Ctx?.ety, Ctx?.SSplit.den_both,
        <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right_assoc,
        <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right,
        <-swap_inner_naturality_outer_right_assoc, <-swap_inner_naturality_right,
      ]
      rw [<-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-E.eff_comm_exchange_assoc hcomm, <-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-Category.assoc, <-Category.assoc, <-Category.assoc]
      rw [
        Category.assoc,
        <-PremonoidalCategory.whiskerLeft_comp_assoc,
        <-PremonoidalCategory.whiskerLeft_comp,
        <-PremonoidalCategory.whiskerLeft_comp,
        -- Category.assoc,
        -- <-tensorHom_def, <-M.copy_rel_tensor er _ (hf := sorry)
      ]
      apply refines_comp _ (by rfl)
      apply refines_whiskerLeft
      apply refines_trans
      apply M.copy_dup_rtimes er _ (hf := IsDup.of_copy_le_pos (le_trans hv.copy_le_quant hq))
      apply refines_of_eq
      simp [ltimes]
    case isFalse h =>
    cases v using Var?.casesZero with
    | zero =>
      apply refines_of_eq
      have hΓr : Γr.del := da.del (by simp)
      simp only [
        SubstSSplit.den', Deriv?.den_zero', den, Var?.ety, ety_var, M.copy_unit, Ty.den,
        swap_inner_tensorUnit_right, Category.assoc, Ctx?.den, Ctx?.ety, Var?.ety, ety_var,
      ]
      rw [
        Ctx?.SSplit.den_drop_tensor_right (σ := Ctx?.erase_right _), Ctx?.PWk.den_refl',
        Category.id_comp, PremonoidalCategory.whiskerLeft_comp_assoc,
        Ctx?.SSplit.den_s12_3_1_23_assoc, tensorHom_def, PremonoidalCategory.whiskerLeft_comp_assoc,
        <-right_exchange (g := _ ◁ !_ Γr.ety)
      ]
      premonoidal
    | rest => simp at h

theorem SubstDS.den_ssplit_neg' (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↞ (σ.ssplit hΔ).den' (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      ssplit, SubstSSplit.erase_left, SubstSSplit.den', den, <-tensorHom_def_of_right,
      Ctx?.SSplit.den_drop_tensor_left, Ctx?.PWk.den_refl'
    ]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hΔ with
  | cons hΔ hlr =>
  simp only [den, tensorHom_def, Category.assoc, Ctx?.SSplit.den]
  rw [<-Central.left_exchange_assoc, <-comp_whiskerRight_assoc]
  have Iσ' :
    css⟦hΓ⟧
    ≫ (σ.den (C := C) ≫ css⟦hΔ⟧) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    ↞ css⟦hΓ⟧
    ≫ (σ.ssplit hΔ).den' (C := C) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    := by apply refines_comp; rfl; apply refines_comp; apply refines_whiskerRight; apply Iσ; rfl
  apply refines_trans _ Iσ'
  cases hlr with
  | left =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_left,
      Category.assoc]
    split
    case isTrue h =>
      simp only [
        SubstSSplit.den', SubstDS.den, Deriv?.den_zero, Ctx?.SSplit.den_drop_tensor_right,
        Ctx?.PWk.den_refl', Category.id_comp, Ctx?.SSplit.den_comm, Category.assoc,
        <-braiding_naturality_left_assoc, <-braiding_naturality_right
      ]
      rw [
        PremonoidalCategory.whiskerLeft_comp_assoc, right_exchange_assoc,
        Ctx?.SSplit.den_s12_3_1_23_assoc
      ]
      congr 1
      simp only [
        comp_whiskerRight_assoc, Ctx?.SSplit.den_comm, <-associator_naturality_left_assoc,
        <-associator_naturality_middle_assoc, <-associator_naturality_right_assoc,
        Ctx?.den, Ctx?.ety, Ty.den, tensorHom_def, PremonoidalCategory.whiskerLeft_comp_assoc,
      ]
      congr 1
      simp only [
        <-comp_whiskerRight_assoc, <-braiding_naturality_right_assoc, <-braiding_naturality_left,
        PremonoidalCategory.whiskerLeft_comp_assoc,
      ]
      simp only [comp_whiskerRight_assoc, <-right_exchange_assoc, left_exchange_assoc]
      congr 3
      simp only [
        braiding_tensor_left, braiding_tensorUnit_left', braiding_tensor_right,
        braiding_tensorUnit_right'
      ]
      calc
      _ = ((β'_ _ _).hom ≫ (β'_ _ _).hom) ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (β'_ _ _).hom
        ≫ (α_ _ _ _).inv
        ≫ _ ◁ (ρ_ _).inv := by premonoidal
      _ = _ := by simp only [symmetry, swap_inner, assoc_inner]; premonoidal
    case isFalse h => cases v using Var?.casesZero with
    | zero =>
      simp only [
        SubstSSplit.den', den, tensorHom_def, Ty.den, Deriv?.unused, Deriv?.den_zero',
        right_exchange (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, Ctx?.den, Ctx?.ety, swap_inner_tensorUnit_right, Category.assoc
      ]
      simp only [
        PremonoidalCategory.whiskerLeft_comp_assoc, comp_whiskerRight_assoc, comp_whiskerRight
      ]
      rw [Ctx?.SSplit.den_s12_3_1_23_assoc, <-right_exchange_assoc, <-right_exchange]
      premonoidal
    | rest => simp at h
  | right =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
      Category.assoc, swap_inner_tensorUnit_right, SubstSSplit.den', Deriv?.den_zero,
      tensorHom_def_of_right, Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
      Category.id_comp, tensor_comp_of_right, PremonoidalCategory.whiskerLeft_comp_assoc,
      Category.assoc, Ctx?.den, Ctx?.ety
    ]
    rw [
      Ctx?.SSplit.den_s12_3_1_23_assoc, tensorHom_def,
      PremonoidalCategory.whiskerLeft_comp_assoc,
      <-swap_whiskerLeft_of_swap (g := da.den)
    ]
    premonoidal
    rw [<-E.eff_comm_exchange hcomm]
  | sboth hv =>
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_sboth,
      Category.assoc]
    split
    case isTrue hv' =>
      have hv : v.copy := hv.copy
      have hΓ : Γr.copy := da.copy hv' hv
      simp only [
        SubstSSplit.den', den, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      ]
      rw [
        <-left_exchange_assoc, <-tensorHom_def_of_right_assoc, Ctx?.SSplit.den_s12_34_13_24_assoc,
        tensorHom_def_assoc
      ]
      apply refines_comp; rfl
      apply refines_comp; rfl
      simp only [
        tensorHom_def, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
        Iso.inv_hom_id_assoc, Ctx?.den, Ty.den, Ctx?.ety, Ctx?.SSplit.den_both,
        <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right_assoc,
        <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right,
        <-swap_inner_naturality_outer_right_assoc, <-swap_inner_naturality_right,
      ]
      rw [<-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-E.eff_comm_exchange_assoc hcomm, <-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-Category.assoc, <-Category.assoc, <-Category.assoc]
      rw [
        Category.assoc,
        <-PremonoidalCategory.whiskerLeft_comp,
        <-PremonoidalCategory.whiskerLeft_comp,
        <-PremonoidalCategory.whiskerLeft_comp_assoc,
        -- Category.assoc,
        -- <-tensorHom_def, <-M.copy_rel_tensor er _ (hf := sorry)
      ]
      apply refines_comp _ (by rfl)
      apply refines_whiskerLeft
      apply refines_trans
      rw [Category.assoc]
      apply M.copy_fuse_rtimes er _ (hf := IsFuse.of_copy_le_neg (le_trans hv.copy_le_quant hq))
    case isFalse h =>
    cases v using Var?.casesZero with
    | zero =>
      apply refines_of_eq
      have hΓr : Γr.del := da.del (by simp)
      simp only [
        SubstSSplit.den', Deriv?.den_zero', den, Var?.ety, ety_var, M.copy_unit, Ty.den,
        swap_inner_tensorUnit_right, Category.assoc, Ctx?.den, Ctx?.ety, Var?.ety, ety_var,
      ]
      rw [
        Ctx?.SSplit.den_drop_tensor_right (σ := Ctx?.erase_right _), Ctx?.PWk.den_refl',
        Category.id_comp, PremonoidalCategory.whiskerLeft_comp_assoc,
        Ctx?.SSplit.den_s12_3_1_23_assoc, tensorHom_def, PremonoidalCategory.whiskerLeft_comp_assoc,
        <-right_exchange (g := _ ◁ !_ Γr.ety)
      ]
      premonoidal
    | rest => simp at h

theorem SubstDS.den_ssplit_pos_right (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↠ (σ.ssplitIn hΔ).den (C := C) ≫ _ ◁ (σ.substRight hΔ).den ≫ (σ.substLeft hΔ).den ▷ _
  := σ.den_ssplit_pos' e hΔ

theorem SubstDS.den_ssplit_neg_right (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↞ (σ.ssplitIn hΔ).den (C := C) ≫ _ ◁ (σ.substRight hΔ).den ≫ (σ.substLeft hΔ).den ▷ _
  := σ.den_ssplit_neg' e hΔ
