import Refinery.Term.Extrinsic.Semantics.Subst.Basic

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PC : PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

theorem SubstDS.den_drop_pos (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] [hΔ : Δ.del]
  : σ.den (C := C) ≫ !_ Δ.ety ↠ (haveI _ : Γ.del := σ.del; !_ Γ.ety)
  := by
  generalize hΔ = hΔ
  induction hσ with
  | nil => simp [den, Ty.den, Ctx?.den]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i v a e el er Γ Γl Γr Δ
    have hv := hΔ.head
    have hΔ : Δ.del := hΔ.tail;
    have hΓl := σ.del;
    have hΓr := da.del hv;
    have hΓd := hΓ.in_del
    simp [den, Ty.den, Ctx?.den, M.drop_tensor]
    rw [<-tensor_comp_of_left_assoc]
    have hΓ : !_ Γ.ety
      = hΓ.den (C := C) ≫ (PremonoidalCategory.tensorHom (!_ Γl.ety) (!_ Γr.ety)) ≫ (λ_ _).hom
      := by rw [<-M.drop_tensor, M.drop_aff ⊥ (B := Γl.ety.tensor Γr.ety)]
    rw [hΓ]
    apply refines_comp; rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ hΔ
    apply M.drop_rem er (f := da.den) (hf := IsRem.of_del_le_pos (le_trans hv.del_le_quant hq))
    rfl

theorem SubstDS.den_drop_neg (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] [hΔ : Δ.del]
  : σ.den (C := C) ≫ !_ Δ.ety ↞ (haveI _ : Γ.del := σ.del; !_ Γ.ety)
  := by
  generalize hΔ = hΔ
  induction hσ with
  | nil => simp [den, Ty.den, Ctx?.den]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i v a e el er Γ Γl Γr Δ
    have hv := hΔ.head
    have hΔ : Δ.del := hΔ.tail;
    have hΓl := σ.del;
    have hΓr := da.del hv;
    have hΓd := hΓ.in_del
    simp [den, Ty.den, Ctx?.den, M.drop_tensor]
    rw [<-tensor_comp_of_left_assoc]
    have hΓ : !_ Γ.ety
      = hΓ.den (C := C) ≫ (PremonoidalCategory.tensorHom (!_ Γl.ety) (!_ Γr.ety)) ≫ (λ_ _).hom
      := by rw [<-M.drop_tensor, M.drop_aff ⊥ (B := Γl.ety.tensor Γr.ety)]
    rw [hΓ]
    apply refines_comp; rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ hΔ
    apply M.drop_add er (f := da.den) (hf := IsAdd.of_del_le_neg (le_trans hv.del_le_quant hq))
    rfl

theorem SubstDS.den_at_pos
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {A} {q : Quant} (hv : Δ.At ⟨A, q⟩ n)
  : σ.den ≫ hv.den ↠ (σ.at hv).den (C := C) := by induction hσ generalizing n with
  | nil => cases hv
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hv with
  | here hd hv =>
    cases da with
    | zero => simp at hv
    | valid A' q da hq' =>
      have hΓl := σ.del;
      cases hv.ty
      simp only [«at», Deriv.cast_rfl, Deriv.den_pwk, den, Var?.ety, ety_var, Deriv?.den_valid,
        tensorHom_def, Ctx?.At.den, ge_iff_le, EQuant.one_le_coe, Var?.Wk.den_used, eqToHom_refl,
        PremonoidalCategory.whiskerLeft_id, Category.comp_id, Category.assoc, ← left_exchange_assoc,
        id_whiskerLeft, Iso.inv_hom_id, <-comp_whiskerRight_assoc,
      ]
      have hda : pw⟦hΓ.pwk_left_del⟧ ≫ da.den (C := C)
        = css⟦hΓ⟧ ≫ (!_ Γl.ety ▷ _) ≫ (λ_ _).hom ≫ da.den
        := by simp [Ctx?.SSplit.den_drop_left_assoc]
      rw [hda]
      apply refines_comp
      rfl
      apply refines_comp
      apply refines_whiskerRight
      apply σ.den_drop_pos el
      rfl
  | there hv hd =>
    have hΓr := da.del hd
    simp only [den, Ctx?.At.den, Category.assoc, ← tensor_comp_of_left_assoc, «at», Deriv.den_pwk,
      Ctx?.SSplit.den_pwk_right_del_assoc, <-rightUnitor_naturality]
    rw [<-tensorHom_def_of_right_assoc]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ
    apply M.drop_rem er (f := da.den) (hf := IsRem.of_del_le_pos (le_trans hd.del_le_quant hq))
    rfl

theorem SubstDS.den_at_neg
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {A} {q : Quant} (hv : Δ.At ⟨A, q⟩ n)
  : σ.den ≫ hv.den ↞ (σ.at hv).den (C := C) := by induction hσ generalizing n with
  | nil => cases hv
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hv with
  | here hd hv =>
    cases da with
    | zero => simp at hv
    | valid A' q da hq' =>
      have hΓl := σ.del;
      cases hv.ty
      simp only [«at», Deriv.cast_rfl, Deriv.den_pwk, den, Var?.ety, ety_var, Deriv?.den_valid,
        tensorHom_def, Ctx?.At.den, ge_iff_le, EQuant.one_le_coe, Var?.Wk.den_used, eqToHom_refl,
        PremonoidalCategory.whiskerLeft_id, Category.comp_id, Category.assoc, ← left_exchange_assoc,
        id_whiskerLeft, Iso.inv_hom_id, <-comp_whiskerRight_assoc,
      ]
      have hda : pw⟦hΓ.pwk_left_del⟧ ≫ da.den (C := C)
        = css⟦hΓ⟧ ≫ (!_ Γl.ety ▷ _) ≫ (λ_ _).hom ≫ da.den
        := by simp [Ctx?.SSplit.den_drop_left_assoc]
      rw [hda]
      apply refines_comp
      rfl
      apply refines_comp
      apply refines_whiskerRight
      apply σ.den_drop_neg el
      rfl
  | there hv hd =>
    have hΓr := da.del hd
    simp only [den, Ctx?.At.den, Category.assoc, ← tensor_comp_of_left_assoc, «at», Deriv.den_pwk,
      Ctx?.SSplit.den_pwk_right_del_assoc, <-rightUnitor_naturality]
    rw [<-tensorHom_def_of_right_assoc]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ
    apply M.drop_add er (f := da.den) (hf := IsAdd.of_del_le_neg (le_trans hd.del_le_quant hq))
    rfl
