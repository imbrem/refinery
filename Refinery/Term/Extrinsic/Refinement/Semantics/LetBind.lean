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

instance DRWS.LetBind.bivalid : BiValid (LetBind (S := S)) C where
  den_eq Dl Dr h := by cases h with
  | bind_op => simp only [Deriv.bv0, Deriv.den, Ctx?.At.den, ge_iff_le, le_refl, Var?.Wk.den_used,
    eqToHom_refl, tensorHom_id, Category.assoc, ← Central.left_exchange_assoc, id_whiskerLeft,
    Iso.inv_hom_id_assoc, Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl', Category.id_comp]
  | bind_let₂ =>
    simp only [Deriv.den, Ty.den, Ctx?.SSplit.den, Var?.SSplit.den_right,
      swap_inner_tensorUnit_right, Category.assoc, Deriv.den_wk2,
      Var?.del.den_unused, eqToHom_refl, PremonoidalCategory.whiskerLeft_id, id_whiskerRight,
      Category.id_comp, Ctx?.den, Var?.ety, Deriv.den_bv0, Ctx?.ety, Ty.den, ety_var, M.drop_unit]
    rw [
      Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
      <-Central.right_exchange_assoc (g := !_ _), PremonoidalCategory.whiskerLeft_comp_assoc,
      <-associator_naturality_middle_assoc, tensorHom_def_of_left, Category.assoc,
      <-comp_whiskerRight_assoc, Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl'
    ]
    premonoidal
  | bind_case =>
    simp only [Deriv.den, Ty.den, Ctx?.SSplit.den, Var?.SSplit.den_right,
      swap_inner_tensorUnit_right, Deriv.den_bv0, EQuant.coe_top,
      PremonoidalCategory.whiskerLeft_comp, Category.assoc, Ctx?.den, Ty.den, Ctx?.ety,
      Deriv.den_wk1, Var?.ety_erase, M.drop_unit, PremonoidalCategory.whiskerLeft_id,
      PremonoidalCategory.id_whiskerRight, Category.id_comp, Var?.ety, ety_var]
    congr 2
    rw [
      <-addHom_desc, <-distl_inv_naturality_left_assoc, Central.left_exchange_assoc,
      <-PremonoidalCategory.whiskerLeft_comp_assoc
    ]
    simp only [<-Central.right_exchange (g := !_ _), ltimes]
    rw [
      PremonoidalCategory.whiskerLeft_comp_assoc, <-associator_naturality_middle_assoc,
      tensorHom_def_of_left, Category.assoc, <-comp_whiskerRight_assoc, Ctx?.SSplit.den_drop_right,
      Ctx?.PWk.den_refl'
    ]
    premonoidal
  | bind_iter =>
    simp only [Deriv.den, Ty.den, Ctx?.SSplit.den, Var?.SSplit.den_right,
      swap_inner_tensorUnit_right, Deriv.den_bv0, EQuant.coe_top, Deriv.den_wk1,
      PremonoidalCategory.whiskerLeft_comp, Ctx?.ety,
      Category.assoc, PremonoidalCategory.whiskerRight_id, comp_whiskerRight, Iso.hom_inv_id_assoc]
    congr 2
    simp only [<-Category.assoc]
    apply Eq.symm
    apply E.pure_uniform
    simp only [
      Category.assoc, Ctx?.den, Ctx?.ety, Ty.den, Var?.ety, ety_var, M.drop_tensor, M.drop_unit,
      tensorHom_id, M.copy_tensor, M.copy_unit, swap_inner_tensorUnit_right,
    ]
    rw [
      Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
    ]
    simp only [<-Central.left_exchange (f := !_ _), ltimes]
    rw [
      PremonoidalCategory.whiskerLeft_comp_assoc, <-associator_naturality_middle_assoc,
      tensorHom_def_of_left, Category.assoc, <-comp_whiskerRight_assoc, Ctx?.SSplit.den_drop_right,
      Ctx?.PWk.den_refl', Category.id_comp, triangle_assoc_comp_right_inv_assoc,
      -- Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
      -- <-PremonoidalCategory.whiskerLeft_comp_assoc, leftUnitor_inv_naturality, Category.assoc,
      -- <-PremonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, PremonoidalCategory.whiskerLeft_id,
      -- Category.comp_id, PremonoidalCategory.whiskerLeft_inv_hom_assoc,
      -- <-PremonoidalCategory.comp_whiskerRight_assoc,
      -- tensorHom_def, Category.assoc, <-rightUnitor_inv_naturality_assoc,
      -- PremonoidalCategory.comp_whiskerRight_assoc,
    ]
    simp only [
      PremonoidalCategory.whiskerLeft_id, PremonoidalCategory.id_whiskerRight, Category.id_comp,
      Category.assoc, addHom_comp_addHom, unitors_equal, rightUnitor_naturality,
    ]
    simp only [PremonoidalCategory.comp_whiskerRight_assoc]
    conv =>
      enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
      rw [<-id_whiskerRight]
      lhs
      rw [<-Iso.hom_inv_id (self := (ρ_ _))]
    rw [
      PremonoidalCategory.comp_whiskerRight, <-addHom_comp_addHom,
      <-distl_inv_naturality_left_assoc]
    slice_lhs 0 3 => skip
    slice_rhs 0 1 => skip
    congr 1
    · premonoidal
    · congr 1
      · premonoidal
      · simp only [Category.assoc]
        rw [
          Central.right_exchange_assoc (f := !_ _ ▷ _),
          <-PremonoidalCategory.whiskerLeft_comp_assoc,
        ]
        simp only [<-Central.right_exchange, ltimes]
        rw [
          PremonoidalCategory.whiskerLeft_comp_assoc, <-associator_naturality_middle_assoc,
          <-comp_whiskerRight_assoc, Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl',
        ]
        premonoidal
