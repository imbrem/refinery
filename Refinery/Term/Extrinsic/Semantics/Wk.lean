import Refinery.Term.Extrinsic.Wk
import Refinery.Term.Extrinsic.Semantics.Typing
import Refinery.Ctx.Semantics
import Refinery.Ctx.Semantics.SplitWk

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open ChosenFiniteCoproducts

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

namespace Term

theorem Deriv.wkD_den {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)} (D : Δ ⊢ a : A)
  : (D.wkD ρ).den (C := C) = ρ.den ≫ D.den
  := by induction D generalizing Γ with
  | let₁ hΓ da db Ia Ib =>
    simp only [
      wkD, den, Ctx?.SSplit.wk_den_assoc, tensorHom_def, Category.assoc,
      <-PremonoidalCategory.whiskerLeft_comp_assoc, <-Ia
    ]
    rw [Central.left_exchange_assoc, Ib]
    simp
  | pair hΓ da db Ia Ib =>
    simp only [
      wkD, den, Ctx?.SSplit.wk_den_assoc, tensorHom_def, Category.assoc, ltimes,
      Central.left_exchange_assoc, Central.left_exchange,
    ]
    rw [Ia, Ib]
    simp [Central.right_exchange_assoc]
  | let₂ hΓ da db Ia Ib =>
    simp only [
      wkD, den, Ctx?.SSplit.wk_den_assoc, tensorHom_def, Category.assoc,
      <-PremonoidalCategory.whiskerLeft_comp_assoc, <-Ia
    ]
    rw [Central.left_exchange_assoc, Ib]
    simp
  | case hΓ da db dc Ia Ib Ic =>
    simp only [wkD, den, Ctx?.SSplit.wk_den_assoc, tensorHom_def, Category.assoc, Ty.den]
    congr 1
    rw [
      Central.left_exchange_assoc, Central.left_exchange_assoc,
      DistributiveCategory.distl_inv_naturality_left_assoc, Ib, Ic,
      <-PremonoidalCategory.whiskerLeft_comp_assoc, Ia
    ]
    simp
  | iter hΓ hc hd da db Ia Ib =>
    simp only [
      wkD, den, Ctx?.SSplit.wk_den_assoc, tensorHom_def, Category.assoc, Ia,
      PremonoidalCategory.whiskerLeft_comp_assoc
    ]
    rw [Central.left_exchange_assoc, Central.left_exchange_assoc]
    congr
    apply Eq.symm
    apply E.pure_uniform
    rw [<-PremonoidalCategory.comp_whiskerRight_assoc, Model.copy_rel_ltimes ⊥, Ib]
    simp only [ltimes, comp_whiskerRight, whisker_assoc, Ty.den.eq_5, Category.assoc,
      Iso.inv_hom_id_assoc, Ctx?.Wk.den, ge_iff_le, le_top, Var?.Wk.den_used, eqToHom_refl,
      tensorHom_id, PremonoidalCategory.whiskerLeft_comp, desc_comp, inl_desc, Category.id_comp,
      inr_desc]
    rw [
      PremonoidalCategory.associator_naturality_left_assoc,
      Central.left_exchange_assoc, Central.left_exchange_assoc,
      DistributiveCategory.distl_inv_naturality_left_assoc
    ]
    simp only [
      desc_comp, Category.assoc, inl_desc, inr_desc, Category.id_comp,
      <-PremonoidalCategory.comp_whiskerRight_assoc, Model.drop_aff ⊥
    ]
  | _ => simp [wkD, den, *]
