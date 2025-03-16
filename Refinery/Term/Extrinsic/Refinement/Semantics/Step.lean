import Refinery.Term.Extrinsic.Refinement.Semantics.Valid
import Refinery.Term.Extrinsic.Refinement.Rewrite

import Discretion.Monoidal.CoherenceLemmas

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open ChosenFiniteCoproducts

open scoped MonoidalCategory

open HasCommRel

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

theorem DRWS.Step.bivalid : BiValid (Step (S := S)) C where
  den_eq Dl Dr h := by cases h with
  | terminal =>
    stop
    simp only [Ty.den, Deriv.den, Ctx?.ety, Var?.ety, ety_var, M.drop_tensor, Model.drop_unit,
      tensorHom_def, PremonoidalCategory.whiskerLeft_id,
      Category.comp_id, Category.assoc, <-Central.left_exchange_assoc,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl', Category.id_comp]
    premonoidal
  | initial =>
    stop
    simp only [Deriv.den]
    congr 2
    apply DistributiveCategory.fromTensorZero_unique
  | let₂_eta =>
    stop
    rename_i Γ b A B
    simp only [Ty.den, Deriv.den, Ctx?.SSplit.den, Ctx?.ety, Var?.SSplit.den_left,
      Var?.SSplit.den_right, swap_inner_tensorUnit_right, Deriv.den_bv1,
      Var?.del.den_unused, eqToHom_refl, PremonoidalCategory.whiskerLeft_id, Category.id_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc, Deriv.den_bv0,
      EQuant.coe_top, M.drop_tensor, tensorHom_id, ltimes, Ctx?.den, Var?.ety, ety_var,
      M.drop_unit, Ctx?.SSplit.den_both, tensorHom_def]
    calc
      _ = css⟦Γ.erase_left⟧
        ≫ t⟦Γ.erase.ety⟧ ◁ Dr.den
        ≫ (α_ t⟦Γ.erase.ety⟧ t⟦A⟧ t⟦B⟧).inv
        ≫ (Δ_ Γ.erase.ety ▷ t⟦A⟧
          ≫ _ ◁ (ρ_ t⟦A⟧).inv
          ≫ (βi_ t⟦Γ.erase.ety⟧ t⟦Γ.erase.ety⟧ t⟦A⟧ (𝟙_ C)).hom
          ≫ !_ Γ.erase.ety ▷ _ ▷ _
          ≫ _ ◁ !_ Γ.erase.ety ▷ _
          ≫ (λ_ t⟦A⟧).hom ▷ _
        ) ▷ t⟦B⟧
        ≫ (α_ _ _ _).hom
        ≫ t⟦A⟧ ◁ ((λ_ (𝟙_ C)).hom ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom)
            := by premonoidal
      _ = css⟦Γ.erase_left⟧
        ≫ t⟦Γ.erase.ety⟧ ◁ Dr.den
        ≫ (α_ t⟦Γ.erase.ety⟧ t⟦A⟧ t⟦B⟧).inv
        ≫ ((Δ_ Γ.erase.ety ≫ !_ Γ.erase.ety ▷ _ ≫ _ ◁ !_ Γ.erase.ety) ▷ t⟦A⟧
          ≫ _ ◁ (ρ_ t⟦A⟧).inv
          ≫ (ρ_ _).hom ▷ _
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (λ_ _).inv
          ≫ (λ_ _).hom ▷ _
        ) ▷ t⟦B⟧
        ≫ (α_ _ _ _).hom
        ≫ t⟦A⟧ ◁ ((λ_ (𝟙_ C)).hom ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom)
            := by
        rw [
          <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_left_assoc,
          swap_inner_tensorUnit_left
        ]
        premonoidal
      _ = css⟦Γ.erase_left⟧
        ≫ t⟦Γ.erase.ety⟧ ◁ Dr.den
        ≫ !_ Γ.erase.ety ▷ _
        ≫ (α_ _ t⟦A⟧ t⟦B⟧).inv
        ≫ ((λ_ _).inv ▷ t⟦A⟧
          ≫ _ ◁ (ρ_ t⟦A⟧).inv
          ≫ (ρ_ _).hom ▷ _
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (λ_ _).inv
          ≫ (λ_ _).hom ▷ _
        ) ▷ t⟦B⟧
        ≫ (α_ _ _ _).hom
        ≫ t⟦A⟧ ◁ ((λ_ (𝟙_ C)).hom ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom)
            := by
            rw [M.copy_drop_left_assoc]
            premonoidal
      _ = _ := by
        rw [<-Central.left_exchange_assoc, Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl']
        premonoidal
  | case_eta =>
    stop
    simp only [Ty.den, Deriv.den, Deriv.den_bv0, EQuant.coe_top, Category.assoc]
    rw [
      <-addHom_desc, <-distl_inv_naturality_left_assoc, <-Central.left_exchange_assoc,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl', Category.id_comp,
      <-leftUnitor_inv_naturality_assoc, leftUnitor_inv_distl_assoc,
    ]
    simp [addHom_comp_addHom, addHom_id]
  | let₂_beta hΓ hΓc Da Db =>
    stop
    simp only [Deriv.den, Ty.den, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      Ctx?.SSplit.den, Var?.SSplit.den_left, Deriv.den_wk0, Var?.del.den_unused, eqToHom_refl,
      PremonoidalCategory.whiskerLeft_id, Category.id_comp, whiskerLeft_rightUnitor, Ctx?.den,
      Var?.ety, Ctx?.ety, ety_var, M.drop_unit, tensorHom_def]
    rw [
      <-Central.left_exchange_assoc,
      Ctx?.SSplit.assoc_inv_coherence_assoc (σ23 := hΓc.comm),
    ]
    congr 1
    rw [<-Ctx?.SSplit.den_comm]
    simp only [PremonoidalCategory.whiskerLeft_comp, tensor_whiskerLeft,
      whiskerLeft_rightUnitor_inv, swap_inner, assoc_inner, PremonoidalCategory.whiskerRight_id,
      whiskerLeft_rightUnitor, Category.assoc, pentagon_hom_hom_inv_inv_hom, Iso.inv_hom_id_assoc,
      pentagon_hom_inv_inv_inv_hom_assoc, Iso.hom_inv_id_assoc]
    congr 1
    simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    rw [BraidedCategory'.braiding_naturality_right_assoc, SymmetricCategory'.symmetry_assoc]
  | case_inl => stop simp [Deriv.den, inl_distl_inv_assoc]
  | case_inr => stop simp [Deriv.den, inr_distl_inv_assoc]
  | fixpoint =>
    simp only [Deriv.den]
    congr 2
    sorry
  | _ => sorry
