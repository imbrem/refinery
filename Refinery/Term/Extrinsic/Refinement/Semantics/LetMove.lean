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
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

-- instance RWS.instLetMoveBivalid : BiValid (LetMove (S := S)) C where
--   den_eq h Dl Dr := by cases h with
--   | let_op hΓ hf da db =>
--     stop
--     rename_i Γ Γr Γl f a A B b
--     have hDl : Dl.den (C := C) = ((da.op hf).let₁ hΓ db).den := by apply Deriv.coherence
--     have hDr : Dr.den (C := C) = (da.let₁ hΓ
--                       (.let₁ (Γl.erase_right.cons (.right _))
--                         (.op hf (.bv (.here inferInstance (by simp)))) (db.wk1 _))).den
--             := by apply Deriv.coherence
--     rw [hDl, hDr]
--     simp only [
--       Deriv.den, Ctx?.SSplit.den, Var?.SSplit.den, Var?.erase, Var?.ety, ety_var,
--       swap_inner_tensorUnit_right, Ty.den, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
--       Deriv.den_wk1, Ctx?.den, Ctx?.ety, Ctx?.At.den, Var?.Wk.den, eqToHom_refl,
--       tensorHom_def, PremonoidalCategory.whiskerLeft_id, Category.id_comp, M.drop_unit
--     ]
--     congr 2
--     simp only [<-Category.assoc]
--     congr 1
--     convert_to t⟦Γl.ety⟧ ◁ hf.den (C := C) =
--       (css⟦Γl.erase_right⟧ ≫ t⟦Γl.ety⟧ ◁ !_ Γl.erase.ety ≫ (ρ_ _).hom) ▷ t⟦A⟧
--         ≫ t⟦Γl.ety⟧ ◁ hf.den
--       using 1
--     premonoidal
--     rw [Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl']
--     simp
--   | let_let₁ hΓ hΓc da db dc =>
--     stop
--     rename_i Γ Y Γr Γl Γc Γm a A b B c
--     have hDl : Dl.den (C := C) = ((da.let₁ hΓc db).let₁ hΓ dc).den := by apply Deriv.coherence
--     have hDr : Dr.den (C := C)
--       = (da.let₁ (hΓ.s1_23_12_3 hΓc) (db.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (dc.wk1 _))).den
--       := by apply Deriv.coherence
--     rw [hDl, hDr]
--     simp only [
--       Deriv.den, Deriv.den_wk1, PremonoidalCategory.whiskerLeft_comp, Category.assoc, Var?.erase,
--       Var?.ety, ety_var, Ctx?.den, Ctx?.ety, Ty.den, M.drop_unit, Ctx?.SSplit.den,
--       Var?.SSplit.den, tensorHom_def, swap_inner_tensorUnit_right,
--     ]
--     rw [
--       <-Central.left_exchange_assoc,
--       <-(hΓ.s1_23_12_3 hΓc).assoc_coherence_assoc (hΓ.s1_23_12 hΓc)]
--     premonoidal
--   | let_let₂ hΓ hΓc da db dc =>
--     stop
--     have hDl : Dl.den (C := C) = ((da.let₂ hΓc db).let₁ hΓ dc).den := by apply Deriv.coherence
--     have hDr : Dr.den (C := C)
--       = (da.let₂ (hΓ.s1_23_12_3 hΓc)
--           (db.let₁ (((hΓ.s1_23_12 hΓc).cons (.right _)).cons (.right _)) ((dc.wk1 _).wk1 _))).den
--       := by apply Deriv.coherence
--     rw [hDl, hDr]
--     simp only [
--       Deriv.den, Deriv.den_wk1, PremonoidalCategory.whiskerLeft_comp, Category.assoc, Var?.erase,
--       Var?.ety, ety_var, Ctx?.den, Ctx?.ety, Ty.den, M.drop_unit, Ctx?.SSplit.den,
--       Var?.SSplit.den, tensorHom_def, swap_inner_tensorUnit_right,
--       PremonoidalCategory.comp_whiskerRight_assoc
--     ]
--     rw [
--       <-associator_inv_naturality_left_assoc,
--       <-Central.left_exchange_assoc,
--       <-(hΓ.s1_23_12_3 hΓc).assoc_coherence_assoc (hΓ.s1_23_12 hΓc)]
--     premonoidal
--   | let_case hΓ hΓc da db dc dd =>
--     stop
--     have hDl : Dl.den (C := C) = ((da.case hΓc db dc).let₁ hΓ dd).den := by apply Deriv.coherence
--     have hDr : Dr.den (C := C)
--       = (da.case (hΓ.s1_23_12_3 hΓc)
--           (db.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (dd.wk1 _))
--           (dc.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (dd.wk1 _))
--         ).den
--       := by apply Deriv.coherence
--     rw [hDl, hDr]
--     simp only [
--       Deriv.den, Deriv.den_wk1, PremonoidalCategory.whiskerLeft_comp, Category.assoc, Var?.erase,
--       Var?.ety, ety_var, Ctx?.den, Ctx?.ety, Ty.den, M.drop_unit, Ctx?.SSplit.den,
--       Var?.SSplit.den, tensorHom_def, swap_inner_tensorUnit_right,
--       PremonoidalCategory.comp_whiskerRight_assoc
--     ]
--     rw [
--       <-addHom_desc,
--       <-distl_inv_naturality_left_assoc,
--       <-Central.left_exchange_assoc,
--       <-(hΓ.s1_23_12_3 hΓc).assoc_coherence_assoc (hΓ.s1_23_12 hΓc),
--       <-associator_naturality_right_assoc]
--     congr 3
--     rw [whiskerLeft_distl_desc_assoc]
--     simp only [desc_comp, Category.assoc, Iso.hom_inv_id_assoc, tensor_whiskerLeft,
--       whiskerRight_tensor, id_whiskerLeft, PremonoidalCategory.whiskerLeft_comp,
--       triangle_assoc_comp_left_inv, triangle_assoc, PremonoidalCategory.whiskerLeft_id,
--       id_whiskerRight, Category.id_comp, inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc,
--       Iso.cancel_iso_inv_left]
--     congr 1 <;> premonoidal
--   | let_abort hΓ da db =>
--     stop
--     rename_i Γ Γr Γl a A b
--     have hDl : Dl.den (C := C) = (da.abort.let₁ hΓ db).den := by apply Deriv.coherence
--     have hDr : Dr.den (C := C) = (da.let₁ hΓ
--                       (.let₁ (Γl.erase_right.cons (.right _))
--                         (.abort (.bv (.here inferInstance (by simp)))) (db.wk1 _))).den
--             := by apply Deriv.coherence
--     rw [hDl, hDr]
--     simp only [
--       Deriv.den, Ctx?.SSplit.den, Var?.SSplit.den, Var?.erase, Var?.ety, ety_var,
--       swap_inner_tensorUnit_right, Ty.den, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
--       Deriv.den_wk1, Ctx?.den, Ctx?.ety, Ctx?.At.den, Var?.Wk.den, eqToHom_refl,
--       tensorHom_def, PremonoidalCategory.whiskerLeft_id, Category.id_comp, M.drop_unit
--     ]
--     congr 2
--     simp only [<-Category.assoc]
--     congr 1
--     convert_to t⟦Γl.ety⟧ ◁ fromZero t⟦A⟧ =
--       (css⟦Γl.erase_right⟧ ≫ t⟦Γl.ety⟧ ◁ !_ Γl.erase.ety ≫ (ρ_ _).hom) ▷ 𝟘_ C
--         ≫ t⟦Γl.ety⟧ ◁ fromZero t⟦A⟧
--       using 1
--     premonoidal
--     rw [Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl']
--     simp
--   | let_iter hΓ hΓc hc hd hcl hdl da db dc =>
--     have hDl : Dl.den (C := C) = ((da.iter hΓc hc hd db).let₁ hΓ dc).den := by apply Deriv.coherence
--     sorry

set_option maxHeartbeats 1000000000 in
instance DRWS.LetMove.bivalid : BiValid (LetMove (S := S)) C where
  den_eq Dl Dr h := by cases h with
  | let_op hΓ hf da db =>
    rename_i Γ Γr Γl f a A B b
    simp only [
      Deriv.den, Ctx?.SSplit.den, Var?.SSplit.den, Var?.erase, Var?.ety, ety_var, Deriv.bv0,
      swap_inner_tensorUnit_right, Ty.den, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      Deriv.den_wk1, Ctx?.den, Ctx?.ety, Ctx?.At.den, Var?.Wk.den, eqToHom_refl,
      tensorHom_def, PremonoidalCategory.whiskerLeft_id, Category.id_comp, M.drop_unit
    ]
    congr 2
    simp only [<-Category.assoc]
    congr 1
    convert_to t⟦Γl.ety⟧ ◁ hf.den (C := C) =
      (css⟦Γl.erase_right⟧ ≫ t⟦Γl.ety⟧ ◁ !_ Γl.erase.ety ≫ (ρ_ _).hom) ▷ t⟦A⟧
        ≫ t⟦Γl.ety⟧ ◁ hf.den
      using 1
    premonoidal
    rw [Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl']
    simp
  | let_let₁ hΓ hΓc da db dc | let_let₂ hΓ hΓc da db dc =>
    simp only [
      Deriv.den, Deriv.den_wk1, PremonoidalCategory.whiskerLeft_comp, Category.assoc, Var?.erase,
      Var?.ety, ety_var, Ctx?.den, Ctx?.ety, Ty.den, M.drop_unit, Ctx?.SSplit.den,
      Var?.SSplit.den, tensorHom_def, swap_inner_tensorUnit_right,
      PremonoidalCategory.comp_whiskerRight_assoc,
      <-associator_inv_naturality_left_assoc,
    ]
    rw [
      <-Central.left_exchange_assoc,
      <-(hΓ.s1_23_12_3 hΓc).assoc_coherence_assoc (hΓ.s1_23_12 hΓc)]
    premonoidal
  | let_case hΓ hΓc da db dc dd =>
    simp only [
      Deriv.den, Deriv.den_wk1, PremonoidalCategory.whiskerLeft_comp, Category.assoc, Var?.erase,
      Var?.ety, ety_var, Ctx?.den, Ctx?.ety, Ty.den, M.drop_unit, Ctx?.SSplit.den,
      Var?.SSplit.den, tensorHom_def, swap_inner_tensorUnit_right,
      PremonoidalCategory.comp_whiskerRight_assoc
    ]
    rw [
      <-addHom_desc,
      <-distl_inv_naturality_left_assoc,
      <-Central.left_exchange_assoc,
      <-(hΓ.s1_23_12_3 hΓc).assoc_coherence_assoc (hΓ.s1_23_12 hΓc),
      <-associator_naturality_right_assoc]
    congr 3
    rw [whiskerLeft_distl_desc_assoc]
    simp only [desc_comp, Category.assoc, Iso.hom_inv_id_assoc, tensor_whiskerLeft,
      whiskerRight_tensor, id_whiskerLeft, PremonoidalCategory.whiskerLeft_comp,
      triangle_assoc_comp_left_inv, triangle_assoc, PremonoidalCategory.whiskerLeft_id,
      id_whiskerRight, Category.id_comp, inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc,
      Iso.cancel_iso_inv_left]
    congr 1 <;> premonoidal
  | let_abort hΓ da db =>
    rename_i Γ Γr Γl a A b
    simp only [
      Deriv.den, Ctx?.SSplit.den, Var?.SSplit.den, Var?.erase, Var?.ety, ety_var, Deriv.bv0,
      swap_inner_tensorUnit_right, Ty.den, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      Deriv.den_wk1, Ctx?.den, Ctx?.ety, Ctx?.At.den, Var?.Wk.den, eqToHom_refl,
      tensorHom_def, PremonoidalCategory.whiskerLeft_id, Category.id_comp, M.drop_unit
    ]
    congr 2
    simp only [<-Category.assoc]
    congr 1
    convert_to t⟦Γl.ety⟧ ◁ fromZero t⟦A⟧ =
      (css⟦Γl.erase_right⟧ ≫ t⟦Γl.ety⟧ ◁ !_ Γl.erase.ety ≫ (ρ_ _).hom) ▷ 𝟘_ C
        ≫ t⟦Γl.ety⟧ ◁ fromZero t⟦A⟧
      using 1
    premonoidal
    rw [Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl']
    simp
  | let_iter hΓ hΓc hc hd hcl hdl da db dc =>
    rename_i Γ X c Γc Γl Γm Γr a A B b
    simp only [
      Deriv.den, Deriv.den_wk1, PremonoidalCategory.whiskerLeft_comp, Category.assoc, Var?.erase,
      Var?.ety, ety_var, Ctx?.den, Ctx?.ety, Ty.den, M.drop_unit, Ctx?.SSplit.den,
      Var?.SSplit.den, tensorHom_def, swap_inner_tensorUnit_right,
      PremonoidalCategory.comp_whiskerRight_assoc, Ctx?.At.den, M.drop_tensor, M.drop_unit,
      Var?.Wk.den, eqToHom_refl, PremonoidalCategory.whiskerLeft_id,
      PremonoidalCategory.id_whiskerRight, Category.id_comp, Deriv.bv0
    ]
    rw [
      <-(hΓ.s1_23_12_3 hΓc).assoc_coherence_assoc (hΓ.s1_23_12 hΓc),
      <-associator_naturality_right_assoc,
      Central.left_exchange_assoc,
    ]
    congr 2
    rw [
      <-Monoidal.iterate_whiskerLeft,
      <-E.naturality,
      <-Category.assoc,
    ]
    apply E.pure_uniform
    simp only [
      Category.assoc,
      <-associator_naturality_middle_assoc,
      <-associator_naturality_right_assoc
    ]
    calc
    _ = _ := by
      simp only [PremonoidalCategory.whiskerLeft_comp_assoc, <-associator_inv_naturality_right_assoc]
      congr 5
      rw [distl_inv_naturality_right_assoc, distl_inv_distl_inv_assoc]
      congr 1
      simp only [
        Ty.den, distl_inv_naturality_left_assoc, addHom_comp_addHom, Category.comp_id,
        PremonoidalCategory.whiskerLeft_id
      ]
      congr 2
      · {
        calc
        _ = _ := by
          rw [
            M.copy_drop_left,
            <-BraidedCategory'.braiding_naturality_right_assoc,
            braiding_tensorUnit_right'
          ]
          premonoidal
        ((Δ_ Γl.ety ≫ !_ Γl.ety ▷ _) ▷ t⟦Γm.ety⟧) ▷ _
        ≫ ((α_ _ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom) ▷ _
        ≫ (_ ◁ ((β'_ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom ≫ (!_ Γm.ety ▷ _) ≫ (λ_ _).hom)) ▷ _
        ≫ (λ_ _).hom ▷ _
        ≫ dc.den
        = _ := by
          simp only [<-Central.left_exchange (f := !_ Γl.ety), ltimes]
          premonoidal
        (Δ_ Γl.ety ▷ t⟦Γm.ety⟧) ▷ _
        ≫ ((α_ t⟦Γl.ety⟧ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom) ▷ _
        ≫ (t⟦Γl.ety⟧ ◁ (β'_ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom ≫ !_ Γl.ety ▷ _) ▷ _
        ≫ (λ_ _).hom ▷ _
        ≫ (!_ Γm.ety ▷ _) ▷ _
        ≫ (λ_ _).hom ▷ _
        ≫ dc.den
        = _ := by
          rw [<-Central.left_exchange_assoc, M.drop_tensor, tensorHom_def]
          premonoidal
        }
      · {
        calc
        _ = _ := by rw [M.copy_drop_right]; premonoidal
        ((Δ_ Γl.ety ≫ (_ ◁ !_ Γl.ety)) ▷ t⟦Γm.ety⟧
        ≫ (α_ _ _ _).hom
          ≫ t⟦Γl.ety⟧ ◁ ((λ_ _).hom ≫ (ρ_ _).inv)) ▷ t⟦A⟧
        ≫ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).inv ▷ _
        ≫ (α_ _ _ t⟦A⟧).hom
        ≫ _ ◁ (λ_ t⟦A⟧).hom
        ≫ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom
        = _ := by
          rw [
            <-BraidedCategory'.braiding_naturality_left,
            braiding_tensorUnit_left'
          ]
          premonoidal
        (Δ_ Γl.ety ▷ t⟦Γm.ety⟧
        ≫ (α_ t⟦Γl.ety⟧ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom
          ≫ t⟦Γl.ety⟧ ◁ ((β'_ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom ≫ _ ◁ !_ Γl.ety)) ▷ t⟦A⟧
        ≫ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).inv ▷ _
        ≫ (α_ _ _ t⟦A⟧).hom
        ≫ _ ◁ (λ_ t⟦A⟧).hom
        ≫ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom
        = _ := by premonoidal
      }
    css⟦hΓ.s1_23_12 hΓc⟧ ▷ t⟦A⟧
      ≫ (α_ _ _ _).hom
      ≫ (_ ◁ (Δ_ Γm.ety ▷ _))
      ≫ _ ◁ (α_ _ _ _).hom
      ≫ (α_ _ _ _).inv
      ≫ _ ◁ db.den
      ≫ ((Δ_ Γl.ety) ▷ _
        ≫ (α_ _ _ _).hom
        ≫ (t⟦Γl.ety⟧ ◁ (β'_ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom)
        ≫ (α_ _ _ _).inv) ▷ _
      ≫ (∂L _ _ _).inv
      ≫ (
          (α_ _ _ _).hom ≫ _ ◁ dc.den ≫ !_ (Γl.ety.tensor Γm.ety) ▷ t⟦X⟧ ≫ (λ_ t⟦X⟧).hom ⊕ₕ
          (α_ _ _ _).hom ≫ _ ◁ !_ Γl.ety ▷ _ ≫ _ ◁ (λ_ t⟦A⟧).hom ≫ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom
        )
      = _ := by
        congr 5
        apply Eq.symm
        apply Central.left_exchange_assoc
    css⟦hΓ.s1_23_12 hΓc⟧ ▷ t⟦A⟧
      ≫ (α_ _ _ _).hom
      ≫ (_ ◁ (Δ_ Γm.ety ▷ _))
      ≫ _ ◁ (α_ _ _ _).hom
      ≫ (α_ _ _ _).inv
      ≫ ((Δ_ Γl.ety) ▷ _
        ≫ (α_ _ _ _).hom
        ≫ (t⟦Γl.ety⟧ ◁ (β'_ t⟦Γl.ety⟧ t⟦Γm.ety⟧).hom)
        ≫ (α_ _ _ _).inv) ▷ _
      ≫ _ ◁ db.den
      ≫ (∂L _ _ _).inv
      ≫ (
          (α_ _ _ _).hom ≫ _ ◁ dc.den ≫ !_ (Γl.ety.tensor Γm.ety) ▷ t⟦X⟧ ≫ (λ_ t⟦X⟧).hom ⊕ₕ
          (α_ _ _ _).hom ≫ _ ◁ !_ Γl.ety ▷ _ ≫ _ ◁ (λ_ t⟦A⟧).hom ≫ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom
        )
      = _ := by
        rw [M.copy_tensor, tensorHom_def_of_left]
        simp only [swap_inner, assoc_inner]
        premonoidal
    css⟦hΓ.s1_23_12 hΓc⟧ ▷ t⟦A⟧
      ≫ (Δ_ (Γl.ety.tensor Γm.ety)) ▷ _
      ≫ (α_ _ _ _).hom
      ≫ _ ◁ (α_ _ _ _).hom
      ≫ _ ◁ _ ◁ db.den
      ≫ (α_ _ _ _).inv
      ≫ (∂L _ _ _).inv
      ≫ (
          (α_ _ _ _).hom ≫ _ ◁ dc.den ≫ !_ (Γl.ety.tensor Γm.ety) ▷ t⟦X⟧ ≫ (λ_ t⟦X⟧).hom ⊕ₕ
          (α_ _ _ _).hom ≫ _ ◁ !_ Γl.ety ▷ _ ≫ _ ◁ (λ_ t⟦A⟧).hom ≫ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom
        )
      = _ := by
        rw [
          <-M.copy_rel_tensor ⊥ (f := css⟦hΓ.s1_23_12 hΓc⟧) (B := Γl.ety.tensor Γm.ety),
          distl_inv_naturality_right_assoc,
          addHom_comp_addHom, PremonoidalCategory.whiskerLeft_comp_assoc,
          PremonoidalCategory.comp_whiskerRight_assoc,
          distl_inv_distl_inv_assoc, addHom_comp_addHom
        ]
        rfl
    (Δ_ (hΓ.c1_23_12 hΓc).ety
      ≫ ((hΓ.s1_23_12 hΓc).den (C := C) ⊗ css⟦hΓ.s1_23_12 hΓc⟧)) ▷ t⟦A⟧
      ≫ (α_ _ _ _).hom
      ≫ _ ◁ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).hom
      ≫ _ ◁ _ ◁ db.den
      ≫ _ ◁ (∂L _ t⟦B⟧ t⟦A⟧).inv
      ≫ _ ◁ (dc.den ⊕ₕ !_ Γl.ety ▷ t⟦A⟧ ≫ (λ_ t⟦A⟧).hom)
      ≫ (∂L _ t⟦X⟧ t⟦A⟧).inv
      ≫ (!_ (Γl.ety.tensor Γm.ety) ▷ t⟦X⟧ ≫ (λ_ t⟦X⟧).hom ⊕ₕ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom)
      = _ := by
        rw [<-distl_inv_naturality_left_assoc,
            <-Central.left_exchange_assoc,
            <-Central.left_exchange_assoc,
            <-Central.left_exchange_assoc,
            tensorHom_def_of_left
          ]
        premonoidal
    Δ_ (hΓ.c1_23_12 hΓc).ety ▷ t⟦A⟧
      ≫ (t⟦(hΓ.c1_23_12 hΓc).ety⟧ ◁ css⟦hΓ.s1_23_12 hΓc⟧) ▷ t⟦A⟧
      ≫ (α_ t⟦(hΓ.c1_23_12 hΓc).ety⟧ _ _).hom
      ≫ _ ◁ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).hom
      ≫ _ ◁ _ ◁ db.den
      ≫ _ ◁ ((∂L _ t⟦B⟧ t⟦A⟧).inv ≫ (dc.den ⊕ₕ !_ Γl.ety ▷ t⟦A⟧ ≫ (λ_ t⟦A⟧).hom))
      ≫ (∂L t⟦(hΓ.c1_23_12 hΓc).ety⟧ t⟦X⟧ t⟦A⟧).inv
      ≫ (css⟦hΓ.s1_23_12 hΓc⟧ ▷ _ ⊕ₕ css⟦hΓ.s1_23_12 hΓc⟧ ▷ _)
      ≫ (!_ (Γl.ety.tensor Γm.ety) ▷ t⟦X⟧ ≫ (λ_ t⟦X⟧).hom ⊕ₕ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom)
      = _ := by
        congr 7
        simp only [
          addHom_comp_addHom, Category.comp_id, <-comp_whiskerRight_assoc, Category.id_comp
        ]
        congr 3
        apply M.drop_aff ⊥ (f := css⟦hΓ.s1_23_12 hΓc⟧)
          (A := (hΓ.c1_23_12 hΓc).ety) (B := Γl.ety.tensor Γm.ety)
    Δ_ (hΓ.c1_23_12 hΓc).ety ▷ t⟦A⟧
      ≫ (t⟦(hΓ.c1_23_12 hΓc).ety⟧ ◁ css⟦hΓ.s1_23_12 hΓc⟧) ▷ t⟦A⟧
      ≫ (α_ t⟦(hΓ.c1_23_12 hΓc).ety⟧ _ _).hom
      ≫ _ ◁ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).hom
      ≫ _ ◁ _ ◁ db.den
      ≫ _ ◁ ((∂L _ t⟦B⟧ t⟦A⟧).inv ≫ (dc.den ⊕ₕ !_ Γl.ety ▷ t⟦A⟧ ≫ (λ_ t⟦A⟧).hom))
      ≫ (∂L t⟦(hΓ.c1_23_12 hΓc).ety⟧ t⟦X⟧ t⟦A⟧).inv
      ≫ (!_ (hΓ.c1_23_12 hΓc).ety ▷ t⟦X⟧ ≫ (λ_ t⟦X⟧).hom ⊕ₕ 𝟙 _)
      ≫ (𝟙 t⟦X⟧ ⊕ₕ css⟦hΓ.s1_23_12 hΓc⟧ ▷ t⟦A⟧ ≫ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom)
      = _ := by
        simp only [Ty.den, distl_inv_naturality_left_assoc, addHom_comp_addHom]
        congr 9 <;> premonoidal
    Δ_ (hΓ.c1_23_12 hΓc).ety ▷ t⟦A⟧
      ≫ (t⟦(hΓ.c1_23_12 hΓc).ety⟧ ◁ css⟦hΓ.s1_23_12 hΓc⟧) ▷ t⟦A⟧
      ≫ (α_ t⟦(hΓ.c1_23_12 hΓc).ety⟧ _ _).hom
      ≫ _ ◁ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).hom
      ≫ _ ◁ _ ◁ db.den
      ≫ _ ◁ (
          (ρ_ t⟦Γl.ety⟧).inv ▷ _
          ≫ (∂L _ t⟦B⟧ t⟦A⟧).inv
          ≫ (((ρ_ t⟦Γl.ety⟧).hom ▷ t⟦B⟧ ≫ dc.den) ⊕ₕ
              (!_ Γl.ety ▷ 𝟙_ C ▷ t⟦A⟧ ≫ (λ_ (𝟙_ C)).hom ▷ t⟦A⟧ ≫ (λ_ t⟦A⟧).hom)))
      ≫ (∂L t⟦(hΓ.c1_23_12 hΓc).ety⟧ t⟦X⟧ t⟦A⟧).inv
      ≫ (!_ (hΓ.c1_23_12 hΓc).ety ▷ t⟦X⟧ ≫ (λ_ t⟦X⟧).hom ⊕ₕ 𝟙 _)
      ≫ (𝟙 t⟦X⟧ ⊕ₕ css⟦hΓ.s1_23_12 hΓc⟧ ▷ t⟦A⟧ ≫ (α_ g⟦Γl⟧ g⟦Γm⟧ t⟦A⟧).hom)
      = _ := by simp only [addHom, Category.assoc]; premonoidal
    | dist_iter => sorry
