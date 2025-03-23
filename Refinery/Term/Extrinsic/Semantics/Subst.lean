import Refinery.Term.Extrinsic.Semantics.Subst.Basic
import Refinery.Term.Extrinsic.Semantics.Subst.DropAt
import Refinery.Term.Extrinsic.Semantics.Subst.SplitLeft
import Refinery.Term.Extrinsic.Semantics.Subst.SplitRight
--TODO: eventually, split comm is not necessary, via split right?
import Refinery.Term.Extrinsic.Semantics.Subst.SplitComm
import Refinery.Term.Extrinsic.Semantics.Subst.DupFuse

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

--TODO: semantic substitution

theorem Deriv.den_substD_pos {eσ ea : ε} (he : eσ ⇀ ea)
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos eσ] {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) [ha : a.HasEff ea] : σ.den ≫ D.den ↠ (D.substD σ).den (C := C)
  := by
  generalize ha = ha
  induction D generalizing Γ with
  | bv => simp [substD, den, SubstDS.den_at_pos_eff eσ]
  | op | inl | inr | abort =>
    cases ha
    simp only [den, substD]; rw [<-Category.assoc]; apply refines_comp; apply_assumption; rfl
  | let₁ hΓ da db Ia Ib =>
    cases ha with | let₁ ha hb =>
    rename_i Γ Γl Γr A B a b
    simp only [den, substD]
    rw [<-Category.assoc]
    apply refines_trans
    apply refines_comp
    apply SubstDS.den_ssplit_pos_eff_right eσ
    rfl
    simp only [Category.assoc]
    apply refines_comp; rfl
    apply refines_trans
    apply refines_comp; rfl
    apply E.eff_left_fwd_assoc he
    rw [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    apply refines_comp
    apply refines_whiskerLeft
    apply Ia _ ha
    convert Ib ((σ.substLeft hΓ).lift _) hb
    rw [SubstDS.den_lift]
  | unit => simp [substD, den, SubstDS.den_drop_pos_eff eσ]
  | pair hΓ da db Ia Ib  =>
    cases ha with | pair ha hb =>
    rename_i Γ Γl Γr A B a b
    simp only [den, substD, ltimes]
    rw [<-Category.assoc]
    apply refines_trans
    apply refines_comp
    apply SubstDS.den_ssplit_pos_eff_left eσ
    rfl
    simp only [Category.assoc]
    apply refines_comp; rfl
    apply refines_trans
    apply refines_comp; rfl
    apply E.eff_right_fwd_assoc he
    rw [<-comp_whiskerRight_assoc, <-PremonoidalCategory.whiskerLeft_comp]
    apply refines_comp
    apply refines_whiskerRight
    apply Ia _ ha
    apply refines_whiskerLeft
    apply Ib _ hb
  | let₂ hΓ da db Ia Ib =>
    cases ha with | let₂ ha hb =>
    rename_i Γ Γl Γr A B C a b
    simp only [den, substD]
    rw [<-Category.assoc]
    apply refines_trans
    apply refines_comp
    apply SubstDS.den_ssplit_pos_eff_right eσ
    rfl
    simp only [Category.assoc]
    apply refines_comp; rfl
    apply refines_trans
    apply refines_comp; rfl
    apply E.eff_left_fwd_assoc he
    rw [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    apply refines_comp
    apply refines_whiskerLeft
    apply Ia _ ha
    simp only [Ty.den, associator_inv_naturality_left_assoc]
    apply refines_comp; rfl
    convert Ib (((σ.substLeft hΓ).lift _).lift _) hb
    simp only [SubstDS.den_lift]
  | case hΓ da db dc Ia Ib Ic =>
    cases ha with | case ha hb hc =>
    rename_i Γ Γl Γr A B C a b c
    simp only [den, substD]
    rw [<-Category.assoc]
    apply refines_trans
    apply refines_comp
    apply SubstDS.den_ssplit_pos_eff_right eσ
    rfl
    simp only [Category.assoc]
    apply refines_comp; rfl
    apply refines_trans
    apply refines_comp; rfl
    apply E.eff_left_fwd_assoc he
    rw [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    apply refines_comp
    apply refines_whiskerLeft
    apply Ia _ ha
    simp only [Ty.den, distl_inv_naturality_left_assoc]
    apply refines_comp; rfl
    rw [addHom_desc]
    apply refines_desc
    convert Ib ((σ.substLeft hΓ).lift _) hb
    rw [SubstDS.den_lift]
    convert Ic ((σ.substLeft hΓ).lift _) hc
    rw [SubstDS.den_lift]
  | iter hΓ hc hd da db Ia Ib =>
    cases ha with | iter hei ha hb =>
    rename_i Γ Γl Γr A B a b
    simp only [den, substD]
    rw [<-Category.assoc]
    apply refines_trans
    apply refines_comp
    apply SubstDS.den_ssplit_pos_eff_right eσ
    rfl
    simp only [Category.assoc]
    apply refines_comp; rfl
    apply refines_trans
    apply refines_comp; rfl
    apply E.eff_left_fwd_assoc he
    rw [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    apply refines_comp
    apply refines_whiskerLeft
    apply Ia _ ha
    apply (E.right_mover_right_uniform he).right_uniform
    apply HasEff.has_eff
    apply HasEff.has_eff
    simp only [Ty.den, Category.assoc]
    rw [<-comp_whiskerRight_assoc]
    apply refines_trans
    apply refines_comp
    apply refines_whiskerRight
    apply SubstDS.den_dup_right_eff eσ
    rfl
    simp only [
      rtimes, comp_whiskerRight, Category.assoc, associator_naturality_left_assoc,
      associator_naturality_middle_assoc
    ]
    apply refines_comp; rfl
    apply refines_comp; rfl
    apply refines_trans
    apply refines_comp; rfl
    apply E.eff_left_fwd_assoc he
    rw [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    apply refines_comp
    apply refines_whiskerLeft
    convert Ib ((σ.substLeft hΓ).lift _) hb
    rw [SubstDS.den_lift]
    rw [distl_inv_naturality_left_assoc, addHom_comp_addHom, addHom_comp_addHom]
    apply refines_comp; rfl
    apply refines_addHom
    rw [<-comp_whiskerRight_assoc, Category.comp_id]
    apply refines_comp
    apply refines_whiskerRight
    apply SubstDS.den_drop_pos_eff eσ
    rfl
    simp
