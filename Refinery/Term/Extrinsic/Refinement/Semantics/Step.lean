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

set_option maxHeartbeats 10000000000 in
theorem DRWS.Step.bivalid : BiValid (Step (S := S)) C where
  den_eq Dl Dr h := by cases h with
  | terminal =>
    simp only [Ty.den, Deriv.den, Ctx?.ety, Var?.ety, ety_var, M.drop_tensor, Model.drop_unit,
      tensorHom_def, PremonoidalCategory.whiskerLeft_id,
      Category.comp_id, Category.assoc, <-Central.left_exchange_assoc,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl', Category.id_comp]
    premonoidal
  | initial =>
    simp only [Deriv.den]
    congr 2
    apply DistributiveCategory.fromTensorZero_unique
  | let₂_eta =>
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
        ≫ (α_ t⟦Γ.erase.ety⟧ _ _).inv
        ≫ (Δ_ Γ.erase.ety ▷ _
          ≫ _ ◁ (ρ_ _).inv
          ≫ (βi_ t⟦Γ.erase.ety⟧ t⟦Γ.erase.ety⟧ _ _).hom
          ≫ !_ Γ.erase.ety ▷ _ ▷ _
          ≫ _ ◁ !_ Γ.erase.ety ▷ _
          ≫ (λ_ _).hom ▷ _
        ) ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ ((λ_ _).hom ▷ _ ≫ (λ_ _).hom)
            := by premonoidal
      _ = css⟦Γ.erase_left⟧
        ≫ t⟦Γ.erase.ety⟧ ◁ Dr.den
        ≫ (α_ t⟦Γ.erase.ety⟧ _ _).inv
        ≫ ((Δ_ Γ.erase.ety ≫ !_ Γ.erase.ety ▷ _ ≫ _ ◁ !_ Γ.erase.ety) ▷ _
          ≫ _ ◁ (ρ_ _).inv
          ≫ (ρ_ _).hom ▷ _
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (λ_ _).inv
          ≫ (λ_ _).hom ▷ _
        ) ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ ((λ_ _).hom ▷ _ ≫ (λ_ _).hom)
            := by
        rw [
          <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_left_assoc,
          swap_inner_tensorUnit_left
        ]
        premonoidal
      _ = css⟦Γ.erase_left⟧
        ≫ t⟦Γ.erase.ety⟧ ◁ Dr.den
        ≫ !_ Γ.erase.ety ▷ _
        ≫ (α_ _ _ _).inv
        ≫ ((λ_ _).inv ▷ _
          ≫ _ ◁ (ρ_ _).inv
          ≫ (ρ_ _).hom ▷ _
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (λ_ _).inv
          ≫ (λ_ _).hom ▷ _
        ) ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ ((λ_ _).hom ▷ _ ≫ (λ_ _).hom)
            := by
            rw [M.copy_drop_left_assoc]
            premonoidal
      _ = _ := by
        rw [<-Central.left_exchange_assoc, Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl']
        premonoidal
  | case_eta =>
    simp only [Ty.den, Deriv.den, Deriv.den_bv0, EQuant.coe_top, Category.assoc]
    rw [
      <-addHom_desc, <-distl_inv_naturality_left_assoc, <-Central.left_exchange_assoc,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl', Category.id_comp,
      <-leftUnitor_inv_naturality_assoc, leftUnitor_inv_distl_assoc,
    ]
    simp [addHom_comp_addHom, addHom_id]
  | let₂_beta hΓ hΓc Da Db =>
    simp only [Deriv.den, Ty.den, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      Ctx?.SSplit.den, Var?.SSplit.den_left, Deriv.den_wk0, Var?.del.den_unused, eqToHom_refl,
      PremonoidalCategory.whiskerLeft_id, Category.id_comp, whiskerLeft_rightUnitor, Ctx?.den,
      Var?.ety, Ctx?.ety, ety_var, M.drop_unit, tensorHom_def]
    rw [
      <-Central.left_exchange_assoc,
      Ctx?.SSplit.assoc_inv_coherence_assoc (σ23 := hΓc.comm),
    ]
    congr 1
    rw [<-Ctx?.SSplit.den_braiding]
    simp only [PremonoidalCategory.whiskerLeft_comp, tensor_whiskerLeft,
      whiskerLeft_rightUnitor_inv, swap_inner, assoc_inner, PremonoidalCategory.whiskerRight_id,
      whiskerLeft_rightUnitor, Category.assoc, pentagon_hom_hom_inv_inv_hom, Iso.inv_hom_id_assoc,
      pentagon_hom_inv_inv_inv_hom_assoc, Iso.hom_inv_id_assoc]
    congr 1
    simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    rw [BraidedCategory'.braiding_naturality_right_assoc, SymmetricCategory'.symmetry_assoc]
  | case_inl => simp [Deriv.den, inl_distl_inv_assoc]
  | case_inr => simp [Deriv.den, inr_distl_inv_assoc]
  | fixpoint hc hd Da hΓ Db =>
    rename_i Γ B Γl Γr a A b
    simp only [
      Deriv.den, Deriv.den_bv0, Deriv.den_wk1, Ctx?.den, Ctx?.ety, Var?.ety, ety_var, Ty.den,
      Var?.erase, M.drop_tensor, M.drop_unit, tensorHom_id, Ctx?.SSplit.den,
      Ctx?.SSplit.den_both, Var?.SSplit.den, swap_inner_tensorUnit_right, M.copy_tensor,
      M.copy_unit, PremonoidalCategory.whiskerLeft_id, Category.assoc, Category.id_comp,
      tensorHom_def,
    ]
    congr 2
    rw [<-Iterate.fixpoint]
    simp only [Category.assoc, associator_naturality_right_assoc, addHom_desc, Category.id_comp]
    congr 2
    rw [
      Central.left_exchange_assoc, distl_inv_naturality_left_assoc, addHom_desc
    ]
    apply Eq.symm
    rw [<-Category.assoc, <-Category.assoc]
    congr 1; premonoidal
    congr 2; premonoidal
    rw [
      <-Category.assoc, <-Category.assoc, <-Category.assoc, <-Category.assoc, <-Category.assoc,
      <-Category.assoc
    ]
    apply E.pure_uniform
    simp only [
      PremonoidalCategory.whiskerLeft_comp_assoc,
      PremonoidalCategory.whiskerLeft_comp,
      PremonoidalCategory.comp_whiskerRight_assoc,
      PremonoidalCategory.comp_whiskerRight,
      addHom_comp_addHom, Category.id_comp, Category.assoc
    ]
    calc
      _ = (css⟦Γl.erase_right⟧ ≫ _ ◁ !_ Γl.erase.ety ≫ (ρ_ _).hom ≫ Δ_ Γl.ety) ▷ _
      ≫ (α_ _ _ _).hom
      ≫ (ρ_ _).inv ▷ _
      ≫ (ρ_ _).inv ▷ _
      ≫ _ ◁ Db.den
      ≫ (∂L _ _ _).inv
      ≫ (!_ Γl.ety ▷ _ ▷ _ ▷ _
      ≫ (λ_ _).hom ▷ _ ▷ _
      ≫ (λ_ _).hom ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _) := by premonoidal
    _ = _ := by
      rw [
        Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl', Category.id_comp,
        Iso.inv_hom_id_assoc, Central.left_exchange_assoc, Central.left_exchange_assoc,
      ]
      congr 3
      simp only [
        Ty.den, distl_inv_naturality_left_assoc, addHom_comp_addHom, Category.comp_id
      ]
      congr 2; premonoidal
      congr 1
      calc
        (ρ_ _).inv ▷ _ = _ := by simp [Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl']
        (css⟦Γl.erase_right⟧ ≫ _ ◁ !_ Γl.erase.ety) ▷ _ ▷ _ = _ := by premonoidal
  | codiag hΓ hc hd Da Db =>
    rename_i Γ B Γl Γr a A b
    simp only [Deriv.den, Ty.den.eq_5, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
      swap_inner_tensorUnit_right, Deriv.den_bv0, Ctx?.ety, Ty.den.eq_3,
      EQuant.coe_top, Category.assoc, PremonoidalCategory.whiskerLeft_comp, Deriv.den_wk1,
      Var?.del.den_unused, eqToHom_refl, PremonoidalCategory.whiskerLeft_id, id_whiskerRight,
      Category.id_comp, triangle_assoc_comp_left_inv,
      triangle_assoc, comp_whiskerRight, Iso.hom_inv_id_assoc, Var?.ety, ety_var,
      Ctx?.den, Ctx?.ety, M.drop_tensor, M.drop_unit, tensorHom_id, M.copy_tensor,
      M.copy_unit, tensorHom_def]
    congr 2
    calc
      _ = iterate (Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ css⟦Γl.erase_left⟧ ▷ _
        ≫ _ ◁ (α_ _ _ _).hom
        ≫ _ ◁ (ρ_ _).inv ▷ _
        ≫ _ ◁ (_ ◁ Db.den ≫ !_ Γl.erase.ety ▷ _ ▷ _)
        ≫ _ ◁ (∂L _ _ _).inv
        ≫ _ ◁ desc
          ((λ_ _).hom ▷ _ ≫ (λ_ _).hom)
          ((λ_ _).hom ▷ _ ≫ (λ_ _).hom ≫ ChosenFiniteCoproducts.inr _ _)
        ≫ (∂L _ _ _).inv ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _))
        := by
          congr 1
          rw [
            <-addHom_desc, <-PremonoidalCategory.whiskerLeft_comp_assoc (f := (∂L _ _ _).inv),
            <-distl_inv_naturality_left_assoc, PremonoidalCategory.whiskerLeft_comp_assoc,
            PremonoidalCategory.whiskerLeft_comp_assoc,
          ]
          premonoidal
      _ = iterate (Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (css⟦Γl.erase_left⟧ ≫ !_ Γl.erase.ety ▷ _) ▷ _
        ≫ _ ◁ (α_ _ _ _).hom
        ≫ _ ◁ (ρ_ _).inv ▷ _
        ≫ _ ◁ _ ◁ Db.den
        ≫ _ ◁ (∂L _ _ _).inv
        ≫ _ ◁ desc
          ((λ_ _).hom ▷ _ ≫ (λ_ _).hom)
          ((λ_ _).hom ▷ _ ≫ (λ_ _).hom ≫ ChosenFiniteCoproducts.inr _ _)
        ≫ (∂L _ _ _).inv ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _))
          := by
            congr 1
            simp only [<-Central.left_exchange (f := !_ _ ▷ _)]
            premonoidal
      _ = iterate (Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ Db.den
        ≫ _ ◁ ((λ_ _).inv ≫ (λ_ _).inv ▷ _ ≫ (∂L _ _ _).inv ≫ desc
          ((λ_ _).hom ▷ _ ≫ (λ_ _).hom)
          ((λ_ _).hom ▷ _ ≫ (λ_ _).hom ≫ ChosenFiniteCoproducts.inr _ _))
        ≫ (∂L _ _ _).inv ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _))
          := by
          congr 1
          rw [Ctx?.SSplit.den_drop_left, Ctx?.PWk.den_refl']
          premonoidal
      _ = iterate (Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ Db.den
        ≫ _ ◁ desc (𝟙 _) (ChosenFiniteCoproducts.inr _ _)
        ≫ (∂L _ _ _).inv ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _))
          := by
          congr 1
          simp only [
            Ty.den, distl_inv_naturality_left_assoc, leftUnitor_inv_distl_assoc, addHom_desc,
            PremonoidalCategory.inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc,
            Iso.inv_hom_id
          ]
      _ = iterate ((Δ_ Γl.ety ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ Db.den
          ≫ (∂L _ _ _).inv
          ≫ (desc
            ((∂L _ _ _).inv ≫ (!_ _ ▷ _ ≫ (λ_ _).hom ≫ ChosenFiniteCoproducts.inl _ _ ⊕ₕ 𝟙 _))
            (ChosenFiniteCoproducts.inr _ _)))
        ≫ desc (𝟙 _) (ChosenFiniteCoproducts.inr _ _))
          := by
          simp only [Category.assoc]
          congr 4
          rw [<-cancel_epi (f := (∂L _ _ _).hom)]
          ext
          · simp only [Ty.den, inl_distl_assoc, desc_comp, Category.assoc, inr_desc,
            Iso.hom_inv_id_assoc, inl_desc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
            PremonoidalCategory.whiskerLeft_id, Category.id_comp]
            congr 1
            ext <;> simp [addHom]
          · simp only [Ty.den, inr_distl_assoc, desc_comp, Category.assoc, inr_desc,
            Iso.hom_inv_id_assoc, inl_desc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
            PremonoidalCategory.whiskerLeft_id, Category.id_comp, inr_distl_inv_assoc]
            simp [addHom]
      _ = _
        := by
        rw [E.codiagonal]
        simp only [
          Category.assoc, addHom_desc, desc_comp, Category.assoc, inr_desc, Category.comp_id,
          Category.id_comp
        ]
        congr 6
        calc
        _ = _ := by rw [M.copy_drop_right]; simp [addHom]
        (Δ_ Γl.ety ≫ _ ◁ !_ Γl.ety) ▷ _
          ≫ (ρ_ _).hom ▷ _
          ≫ (∂L _ _ _).inv
          ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _)
          = _ := by premonoidal
      iterate (
        iterate (
            Δ_ Γl.ety ▷ _
            ≫ (α_ _ _ _).hom
            ≫ _ ◁ Db.den
            ≫ (∂L _ _ _).inv
            ≫ (Δ_ Γl.ety ▷ _ ≫ (_ ◁ (ρ_ _).inv) ▷ _
                ≫ (α_ _ _ _).hom
                ≫ (_ ◁ (!_ Γl.ety ▷ _ ▷ _ ≫ (λ_ _).hom ▷ _ ≫ (λ_ _).hom)
                ≫ (∂L _ _ _).inv
                ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _)
              )
              ⊕ₕ 𝟙 _)
           )
        )
        = _ := by
        congr 1
        apply Eq.symm
        apply E.pure_uniform
        simp only [Category.assoc, Var?.ety, ety_var, addHom_comp_addHom, Category.comp_id]
        calc
          _ = (Δ_ Γl.ety ≫ _ ◁ Δ_ Γl.ety) ▷ _
            ≫ (α_ _ _ _).hom
            ≫ _ ◁ (α_ _ _ _).hom
            ≫ _ ◁ (ρ_ _).inv ▷ _
            ≫ (α_ _ _ _).inv
            ≫ _ ◁ Db.den
            ≫ (∂L _ _ _).inv
            ≫ ((α_ _ _ _).hom
            ≫ _ ◁ (!_ Γl.ety ▷ _ ▷ _ ≫ (λ_ (_)).hom ▷ _ ≫ (λ_ _).hom)
            ≫ (∂L _ _ _).inv
            ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _) ⊕ₕ (α_ _ _ _).hom) := by premonoidal
          _ = Δ_ Γl.ety ▷ _
            ≫ (α_ _ _ _).hom
            ≫ Δ_ Γl.ety ▷ _
            ≫ _ ◁ Db.den
            ≫ (_ ◁ (ρ_ _).inv) ▷ _
            ≫ (∂L _ _ _).inv
            ≫ ((α_ _ _ _).hom
            ≫ _ ◁ (!_ Γl.ety ▷ _ ▷ _ ≫ (λ_ (_)).hom ▷ _ ≫ (λ_ _).hom)
            ≫ (∂L _ _ _).inv
            ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _) ⊕ₕ (α_ _ _ _).hom)
            := by rw [<-M.copy_assoc]; premonoidal
          _ = _ := by
            rw [Central.left_exchange_assoc]
            simp only [Ty.den, distl_inv_naturality_left_assoc, addHom_comp_addHom]
            congr 5
            premonoidal
      iterate ((Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (ρ_ _).inv ▷ _)
        ≫ iterate (
            _ ◁ Δ_ Γl.ety ▷ _ ▷ _
            ≫ _ ◁ (ρ_ _).hom ▷ _
            ≫ _ ◁ (α_ _ _ _).hom
            ≫ _ ◁ (ρ_ _).inv ▷ _
            ≫ (α_ _ _ _).inv
            ≫ _ ◁ Db.den
            ≫ (∂L _ _ _).inv
            ≫ ((α_ _ _ _).hom ≫ (
                _ ◁ (!_ Γl.ety ▷ _ ▷ _≫ (λ_ _).hom ▷ _ ≫ (λ_ _).hom) ≫
                (∂L _ _ _).inv ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _)
              )
              ⊕ₕ (α_ _ _ _).hom)
           )
        )
        = _ := by
        congr 3
        simp only [
          Ty.den, distl_inv_naturality_right_assoc, addHom_comp_addHom, Category.comp_id,
          PremonoidalCategory.whiskerLeft_id, distl_inv_distl_inv_assoc
        ]
        premonoidal
      iterate ((Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (ρ_ _).inv ▷ _)
        ≫ iterate (
            _ ◁ (Δ_ Γl.ety ▷ _ ▷ _
              ≫ (ρ_ _).hom ▷ _
              ≫ (α_ _ _ _).hom
              ≫ (ρ_ _).inv ▷ _
              ≫ _ ◁ Db.den)
            ≫ _ ◁ (∂L _ _ _).inv
            ≫ _ ◁ (!_ Γl.ety ▷ _ ▷ _≫ (λ_ _).hom ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _)
            ≫ (∂L _ _ _).inv
            ≫ (((∂L _ _ _).inv ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _)) ⊕ₕ 𝟙 _)
           )
        )
        = _ := by
          simp only [Category.assoc]
          rw [<-E.naturality]
          congr 5
          simp only [addHom_comp_addHom, Category.assoc, Category.id_comp]
          premonoidal
      iterate (Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (ρ_ _).inv ▷ _
        ≫ iterate (_ ◁ (Δ_ Γl.ety ▷ _ ▷ _
              ≫ (_ ◁ (λ_ _).inv) ▷ _
              ≫ (α_ _ _ _).hom ▷ _
              ≫ (_ ◁ _ ◁ (λ_ _).hom) ▷ _
              ≫ (ρ_ _).inv ▷ _ ▷ _
              ≫ (α_ _ _ _).hom
              ≫ _ ◁ (ρ_ _).hom ▷ _
              ≫ _ ◁ Db.den
              ≫ (∂L _ _ _).inv
              ≫ (!_ Γl.ety ▷ _ ▷ _≫ (λ_ _).hom ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _))
            ≫ (∂L _ _ _).inv
           )
        ≫ (∂L _ _ _).inv
        ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _)
        )
        = _ := by
          congr 1
          rw [Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl', <-E.iterate_whiskerLeft]
          premonoidal
      iterate (Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (css⟦Γl.erase_right⟧ ≫ _ ◁ !_ Γl.erase.ety) ▷ _
        ≫ _ ◁ iterate (Δ_ Γl.ety ▷ _ ▷ _
           ≫ (_ ◁ (λ_ _).inv) ▷ _
           ≫ (α_ _ _ _).hom ▷ _
           ≫ (_ ◁ _ ◁ (λ_ _).hom) ▷ _
           ≫ (ρ_ _).inv ▷ _ ▷ _
           ≫ (α_ _ _ _).hom
           ≫ _ ◁ (ρ_ _).hom ▷ _
           ≫ _ ◁ Db.den
           ≫ (∂L _ _ _).inv
           ≫ (!_ Γl.ety ▷ _ ▷ _≫ (λ_ _).hom ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _))
        ≫ (∂L _ _ _).inv
        ≫ (!_ Γl.ety ▷ _ ≫ (λ_ _).hom ⊕ₕ 𝟙 _))
        = _ := by congr 1; premonoidal
