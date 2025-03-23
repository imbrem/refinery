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

theorem SubstDS.den_dup_right_eff (e : ε) {Γ Δ : Ctx? α} [hΓ : Γ.copy] [hΔ : Δ.copy]
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e]
  : σ.den (C := C) ≫ Δ_ Δ.ety ↠ Δ_ Γ.ety ≫ _ ◁ σ.den ≫ σ.den ▷ _
  := by
  generalize hΓ = hΓc; generalize hΔ = hΔ
  induction hσ with
  | nil =>
    apply refines_of_eq; simp [den, <-tensorHom_def_of_left]; apply Eq.symm; apply M.copy_drop_both
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i v a e el er Γ Γl Γr Δ
    have hv := hΔ.head
    have hΔ := hΔ.tail
    have hΓl := hΓ.left_copy
    have hΓr := hΓ.right_copy
    simp only [Ctx?.ety, Ty.den, den, M.copy_tensor, Category.assoc, ←tensor_comp_of_left_assoc,
      PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
    rw [
      <-left_exchange_assoc, <-tensorHom_def_of_left_assoc,
      <-M.copy_rel_tensor_assoc ⊥ (B := Γl.ety.tensor Γr.ety), M.copy_tensor_assoc,
    ]
    apply refines_comp; rfl
    conv => rhs; simp only [
      tensorHom_def, PremonoidalCategory.whiskerLeft_comp,
      PremonoidalCategory.whiskerLeft_comp_assoc, comp_whiskerRight, comp_whiskerRight_assoc,
      Category.assoc, <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right_assoc,
      <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right, Ctx?.den, Ty.den,
      Ctx?.ety
    ]
    simp only [<-Category.assoc]
    apply refines_comp
    simp only [Category.assoc]
    apply refines_trans
    apply refines_tensorHom
    apply Iσ hΓl hΔ
    apply M.copy_dup_rtimes er _ (hf := IsDup.of_copy_le_pos (le_trans hv.copy_le_quant hq))
    simp only [
      tensorHom_def, comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp, Category.assoc]
    apply refines_comp; rfl
    rw [<-right_exchange_assoc]
    apply refines_comp; rfl
    conv => rhs; rw [<-E.eff_comm_exchange_assoc hcomm]
    rw [<-right_exchange_assoc]
    rfl

theorem SubstDS.den_fuse_right_eff (e : ε) {Γ Δ : Ctx? α} [hΓ : Γ.copy] [hΔ : Δ.copy]
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e]
  : σ.den (C := C) ≫ Δ_ Δ.ety ↞ Δ_ Γ.ety ≫ _ ◁ σ.den ≫ σ.den ▷ _
  := by
  generalize hΓ = hΓc; generalize hΔ = hΔ
  induction hσ with
  | nil =>
    apply refines_of_eq; simp [den, <-tensorHom_def_of_left]; apply M.copy_drop_both
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i v a e el er Γ Γl Γr Δ
    have hv := hΔ.head
    have hΔ := hΔ.tail
    have hΓl := hΓ.left_copy
    have hΓr := hΓ.right_copy
    simp only [Ctx?.ety, Ty.den, den, M.copy_tensor, Category.assoc, ←tensor_comp_of_left_assoc,
      PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
    rw [
      <-left_exchange_assoc, <-tensorHom_def_of_left_assoc,
      <-M.copy_rel_tensor_assoc ⊥ (B := Γl.ety.tensor Γr.ety), M.copy_tensor_assoc,
    ]
    apply refines_comp; rfl
    conv => lhs; simp only [
      tensorHom_def, PremonoidalCategory.whiskerLeft_comp,
      PremonoidalCategory.whiskerLeft_comp_assoc, comp_whiskerRight, comp_whiskerRight_assoc,
      Category.assoc, <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right_assoc,
      <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right, Ctx?.den, Ty.den,
      Ctx?.ety
    ]
    simp only [<-Category.assoc]
    apply refines_comp
    simp only [Category.assoc]
    apply refines_trans
    swap
    apply refines_tensorHom
    apply Iσ hΓl hΔ
    apply M.copy_fuse_rtimes er _ (hf := IsFuse.of_copy_le_neg (le_trans hv.copy_le_quant hq))
    simp only [
      tensorHom_def, comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp, Category.assoc]
    apply refines_comp; rfl
    rw [<-right_exchange_assoc]
    apply refines_comp; rfl
    conv => lhs; rw [<-E.eff_comm_exchange_assoc hcomm]
    rw [<-right_exchange_assoc]
    rfl
