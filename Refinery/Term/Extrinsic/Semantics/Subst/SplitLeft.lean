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

theorem SubstDS.den_ssplit_pos_eff (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↠ (σ.ssplit hΔ).den (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      ssplit, SubstSSplit.erase_left, SubstSSplit.den, den, tensorHom_def,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl'
    ]
    rw [leftUnitor_inv_naturality]; rfl
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
    ≫ (σ.ssplit hΔ).den (C := C) ▷ _
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
      simp only [SubstSSplit.den, den, tensorHom_def, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc, <-Ctx?.SSplit.den_braiding,
        <-BraidedCategory'.braiding_naturality_right_assoc
      ]
      rw [
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn.comm)
      ]
      congr 1
      simp only [← Ctx?.SSplit.den_braiding, comp_whiskerRight,
        BraidedCategory'.braiding_naturality_right_assoc, BraidedCategory'.braiding_tensor_right,
        Category.assoc, Iso.inv_hom_id_assoc, Deriv?.den_zero, Iso.hom_inv_id_assoc,
        associator_inv_naturality_middle_assoc]
      rw [Central.right_exchange_assoc, E.eff_comm_exchange_assoc hcomm.symm]
      calc
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ ((β'_ _ _).hom
            ≫ (_ ◁ (σ.ssplit hΔ).substLeft.den)
            ≫ (β'_ _ _).hom) ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ (β'_ _ _).hom
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (css⟦(σ.ssplit hΔ).inRight.erase_right⟧
            ≫ _ ◁ !_ (σ.ssplit hΔ).inRight.erase.ety)
          ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ▷ _
          ≫ (_ ◁ da.den) ▷ _ := by
            rw [right_exchange (g := _ ◁ !_ _)]
            simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
            rw [<-right_exchange (g := !_ _)]
            premonoidal
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ (σ.ssplit hΔ).substLeft.den ▷ _ ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ ((β'_ _ _).hom ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ≫ da.den ▷ _)
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (ρ_ _).inv := by
            simp only [
              BraidedCategory'.braiding_naturality_right, SymmetricCategory'.symmetry_assoc,
              Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl', Category.id_comp
            ]
            premonoidal
        _ = _ := by
          congr 2
          rw [
            <-BraidedCategory'.braiding_naturality_left_assoc,
            <-BraidedCategory'.braiding_naturality_right,
          ]
          simp only [swap_inner, assoc_inner]
          premonoidal
    case isFalse h => cases v using Var?.casesZero with
    | zero =>
      simp only [
        SubstSSplit.den, den, tensorHom_def, Ty.den, Deriv?.unused, Deriv?.den_zero',
        right_exchange (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, Ctx?.den, Ctx?.ety, swap_inner_tensorUnit_right
      ]
      simp only [PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight_assoc]
      rw [
        right_exchange_assoc, right_exchange_assoc,
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn)
      ]
      premonoidal
    | rest => simp at h
  | right =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
      Category.assoc, swap_inner_tensorUnit_right, SubstSSplit.den, Deriv?.den_zero,
      tensorHom_def_of_right, Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
      Category.id_comp, tensor_comp_of_right
    ]
    rw [
      <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn),
    ]
    simp only [tensorHom_def]
    premonoidal
  | sboth hv =>
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_sboth,
      Category.assoc]
    split
    case isTrue hv' =>
      have hv : v.copy := hv.copy
      have hΓ : Γr.copy := da.copy hv' hv
      simp only [SubstSSplit.den, den, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      ]
      rw [tensor_comp_of_right, Ctx?.SSplit.den_s12_34_13_24_assoc, tensorHom_def_assoc]
      apply refines_comp; rfl
      apply refines_comp; rfl
      simp only [
        tensorHom_def, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
        Iso.inv_hom_id_assoc, Ctx?.den, Ty.den, Ctx?.ety, Ctx?.SSplit.den_both,
        <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right_assoc,
        <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right
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
      apply M.copy_dup_ltimes er _ (hf := IsDup.of_copy_le_pos (le_trans hv.copy_le_quant hq))
      apply refines_of_eq
      simp [ltimes]
    case isFalse h =>
    cases v using Var?.casesZero with
    | zero =>
      apply refines_of_eq
      have hΓr : Γr.del := da.del (by simp)
      simp only [
        SubstSSplit.den, Deriv?.den_zero', den, Var?.ety, ety_var, M.copy_unit, Ty.den,
        swap_inner_tensorUnit_right, Category.assoc, Ctx?.den, Ctx?.ety, Var?.ety, ety_var
      ]
      rw [
        tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc,
        right_exchange_assoc, Ctx?.SSplit.den_drop_right_assoc, <-rightUnitor_inv_naturality_assoc,
        Category.assoc, Ctx?.SSplit.pwk_den_assoc, tensorHom_def (f := _ ≫ _),
        PremonoidalCategory.whiskerLeft_comp, right_exchange_assoc,
        <-Ctx?.SSplit.den_unstrict, Ctx?.Split.den_wkOut_assoc, <-Ctx?.SSplit.den_unstrict,
        Ctx?.Split.den_wkOutR_assoc, tensorHom_def
      ]
      congr 1
      apply Ctx?.Split.coherence
      premonoidal
    | rest => simp at h

theorem SubstDS.den_ssplit_neg_eff (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↞ (σ.ssplit hΔ).den (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      ssplit, SubstSSplit.erase_left, SubstSSplit.den, den, tensorHom_def,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl'
    ]
    rw [leftUnitor_inv_naturality]; rfl
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
    ≫ (σ.ssplit hΔ).den (C := C) ▷ _
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
      simp only [SubstSSplit.den, den, tensorHom_def, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc, <-Ctx?.SSplit.den_braiding,
        <-BraidedCategory'.braiding_naturality_right_assoc
      ]
      rw [
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn.comm)
      ]
      congr 1
      simp only [← Ctx?.SSplit.den_braiding, comp_whiskerRight,
        BraidedCategory'.braiding_naturality_right_assoc, BraidedCategory'.braiding_tensor_right,
        Category.assoc, Iso.inv_hom_id_assoc, Deriv?.den_zero, Iso.hom_inv_id_assoc,
        associator_inv_naturality_middle_assoc]
      rw [Central.right_exchange_assoc, E.eff_comm_exchange_assoc hcomm.symm]
      calc
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ ((β'_ _ _).hom
            ≫ (_ ◁ (σ.ssplit hΔ).substLeft.den)
            ≫ (β'_ _ _).hom) ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ (β'_ _ _).hom
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (css⟦(σ.ssplit hΔ).inRight.erase_right⟧
            ≫ _ ◁ !_ (σ.ssplit hΔ).inRight.erase.ety)
          ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ▷ _
          ≫ (_ ◁ da.den) ▷ _ := by
            rw [right_exchange (g := _ ◁ !_ _)]
            simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
            rw [<-right_exchange (g := !_ _)]
            premonoidal
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ (σ.ssplit hΔ).substLeft.den ▷ _ ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ ((β'_ _ _).hom ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ≫ da.den ▷ _)
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (ρ_ _).inv := by
            simp only [
              BraidedCategory'.braiding_naturality_right, SymmetricCategory'.symmetry_assoc,
              Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl', Category.id_comp
            ]
            premonoidal
        _ = _ := by
          congr 2
          rw [
            <-BraidedCategory'.braiding_naturality_left_assoc,
            <-BraidedCategory'.braiding_naturality_right,
          ]
          simp only [swap_inner, assoc_inner]
          premonoidal
    case isFalse h => cases v using Var?.casesZero with
    | zero =>
      simp only [
        SubstSSplit.den, den, tensorHom_def, Ty.den, Deriv?.unused, Deriv?.den_zero',
        right_exchange (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, Ctx?.den, Ctx?.ety, swap_inner_tensorUnit_right
      ]
      simp only [PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight_assoc]
      rw [
        right_exchange_assoc, right_exchange_assoc,
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn)
      ]
      premonoidal
    | rest => simp at h
  | right =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
      Category.assoc, swap_inner_tensorUnit_right, SubstSSplit.den, Deriv?.den_zero,
      tensorHom_def_of_right, Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
      Category.id_comp, tensor_comp_of_right
    ]
    rw [
      <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn),
    ]
    simp only [tensorHom_def]
    premonoidal
  | sboth hv =>
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_sboth,
      Category.assoc]
    split
    case isTrue hv' =>
      have hv : v.copy := hv.copy
      have hΓ : Γr.copy := da.copy hv' hv
      simp only [SubstSSplit.den, den, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      ]
      rw [tensor_comp_of_right, Ctx?.SSplit.den_s12_34_13_24_assoc, tensorHom_def_assoc]
      apply refines_comp; rfl
      apply refines_comp; rfl
      simp only [
        tensorHom_def, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
        Iso.inv_hom_id_assoc, Ctx?.den, Ty.den, Ctx?.ety, Ctx?.SSplit.den_both,
        <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right_assoc,
        <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right
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
        Category.assoc,
      ]
      apply refines_comp _ (by rfl)
      apply refines_whiskerLeft
      apply refines_trans
      apply M.copy_fuse_ltimes er da.den
        (hf := IsFuse.of_copy_le_neg (le_trans hv.copy_le_quant hq));
      apply refines_of_eq
      simp [ltimes]
    case isFalse h =>
    cases v using Var?.casesZero with
    | zero =>
      apply refines_of_eq; apply Eq.symm
      have hΓr : Γr.del := da.del (by simp)
      simp only [
        SubstSSplit.den, Deriv?.den_zero', den, Var?.ety, ety_var, M.copy_unit, Ty.den,
        swap_inner_tensorUnit_right, Category.assoc, Ctx?.den, Ctx?.ety, Var?.ety, ety_var
      ]
      rw [
        tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc,
        right_exchange_assoc, Ctx?.SSplit.den_drop_right_assoc, <-rightUnitor_inv_naturality_assoc,
        Category.assoc, Ctx?.SSplit.pwk_den_assoc, tensorHom_def (f := _ ≫ _),
        PremonoidalCategory.whiskerLeft_comp, right_exchange_assoc,
        <-Ctx?.SSplit.den_unstrict, Ctx?.Split.den_wkOut_assoc, <-Ctx?.SSplit.den_unstrict,
        Ctx?.Split.den_wkOutR_assoc, tensorHom_def
      ]
      congr 1
      apply Ctx?.Split.coherence
      premonoidal
    | rest => simp at h

theorem SubstDS.den_ssplit_pos_eff_tensor (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↠ (σ.ssplitIn hΔ).den (C := C) ≫ ((σ.substLeft hΔ).den ⊗ (σ.substRight hΔ).den)
  := σ.den_ssplit_pos_eff e hΔ

theorem SubstDS.den_ssplit_neg_eff_tensor (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↞ (σ.ssplitIn hΔ).den (C := C) ≫ ((σ.substLeft hΔ).den ⊗ (σ.substRight hΔ).den)
  := σ.den_ssplit_neg_eff e hΔ

theorem SubstDS.den_ssplit_pos_eff_left (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↠ (σ.ssplitIn hΔ).den (C := C) ≫ (σ.substLeft hΔ).den ▷ _ ≫ _ ◁ (σ.substRight hΔ).den
  := by convert σ.den_ssplit_pos_eff_tensor e hΔ; simp only [tensorHom_def]

theorem SubstDS.den_ssplit_neg_eff_left (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↞ (σ.ssplitIn hΔ).den (C := C) ≫ (σ.substLeft hΔ).den ▷ _ ≫ _ ◁ (σ.substRight hΔ).den
  := by convert σ.den_ssplit_neg_eff_tensor e hΔ; simp only [tensorHom_def]

theorem SubstDS.den_ssplit_pos {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.HasPos] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↠ (σ.ssplit hΔ).den (C := C)
  := have ⟨⟨e, _⟩⟩ := hσ; σ.den_ssplit_pos_eff e hΔ

theorem SubstDS.den_ssplit_neg {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.HasNeg] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↞ (σ.ssplit hΔ).den (C := C)
  := have ⟨⟨e, _⟩⟩ := hσ; σ.den_ssplit_neg_eff e hΔ

theorem SubstDS.den_ssplit_pos_tensor {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.HasPos] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↠ (σ.ssplitIn hΔ).den (C := C) ≫ ((σ.substLeft hΔ).den ⊗ (σ.substRight hΔ).den)
  := have ⟨⟨e, _⟩⟩ := hσ; σ.den_ssplit_pos_eff_tensor e hΔ

theorem SubstDS.den_ssplit_neg_tensor {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.HasNeg] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↞ (σ.ssplitIn hΔ).den (C := C) ≫ ((σ.substLeft hΔ).den ⊗ (σ.substRight hΔ).den)
  := have ⟨⟨e, _⟩⟩ := hσ; σ.den_ssplit_neg_eff_tensor e hΔ

theorem SubstDS.den_ssplit_pos_left {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.HasPos] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↠ (σ.ssplitIn hΔ).den (C := C) ≫ (σ.substLeft hΔ).den ▷ _ ≫ _ ◁ (σ.substRight hΔ).den
  := have ⟨⟨e, _⟩⟩ := hσ; σ.den_ssplit_pos_eff_left e hΔ

theorem SubstDS.den_ssplit_neg_left {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.HasNeg] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↞ (σ.ssplitIn hΔ).den (C := C) ≫ (σ.substLeft hΔ).den ▷ _ ≫ _ ◁ (σ.substRight hΔ).den
  := have ⟨⟨e, _⟩⟩ := hσ; σ.den_ssplit_neg_eff_left e hΔ

theorem SubstDS.den_ssplit_bivalid {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Bivalid] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).den (C := C) = σ.den ≫ hΔ.den
  := refines_antisymm (σ.den_ssplit_neg hΔ) (σ.den_ssplit_pos hΔ)

theorem SubstDS.den_ssplit_bivalid_tensor {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Bivalid] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  = (σ.ssplitIn hΔ).den (C := C)
  ≫ (tensorHom (σ.substLeft hΔ).den (σ.substRight hΔ).den)
  := by rw [<-den_ssplit_bivalid]; rfl

theorem SubstDS.den_ssplit_bivalid_left {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Bivalid] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  = (σ.ssplitIn hΔ).den (C := C) ≫ (σ.substLeft hΔ).den ▷ _ ≫ _ ◁ (σ.substRight hΔ).den
  := by rw [den_ssplit_bivalid_tensor, tensorHom_def]
