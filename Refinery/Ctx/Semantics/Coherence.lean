import Refinery.Ctx.Semantics

namespace Refinery

open CategoryTheory

open PremonoidalCategory MonoidalCategory'

open scoped MonoidalCategory

open EffectfulCategory

section Braided

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [ChosenFiniteCoproducts C]
         [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε]
         [M : Model φ α ε C]

theorem Var?.Wk.ety_coherence {v w : Var? α} (ρ : v.Wk w) (h : v.ety = w.ety)
  : ρ.den (C := C) = eqToHom (by rw [h]) := by
  cases v with | mk A q => cases w with | mk B q' =>
  cases q using EQuant.casesZero with
  | zero => cases q' using EQuant.casesZero <;> simp
  | rest => cases q' using EQuant.casesZero with
  | zero => cases h; simp [M.drop_unit]
  | rest => rfl

theorem Var?.Wk.quant_coherence {A : Ty α} {q q' : Quant} {w} (ρ : Wk ⟨A, q⟩ w) (ρ' : Wk ⟨A, q'⟩ w)
  : ρ.den (C := C) = ρ'.den (C := C)
  := by cases w using Var?.casesZero <;> simp

theorem Ctx?.ety_eq_length_eq {Γ Δ : Ctx? α} (h : Γ.ety = Δ.ety)
  : Γ.length = Δ.length := by induction Γ generalizing Δ with
  | nil => cases Δ with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ I => cases Δ with
    | nil => cases h
    | cons _ _ => simp only [length_cons, add_left_inj]; apply I; simp at h; exact h.left

theorem Ctx?.PWk.ety_coherence {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) (h : Γ.ety = Δ.ety)
  : ρ.den (C := C) = eqToHom (by rw [Ctx?.den, h]) := by induction ρ with
  | nil => rfl
  | cons _ _ I =>
    simp only [den]
    simp [ety] at h
    rw [I h.left, Var?.Wk.ety_coherence _ h.right, PremonoidalCategory.eqToHom_tensorHom]

theorem Ctx?.Wk.ety_coherence {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) (h : Γ.ety = Δ.ety)
  : ρ.den (C := C) = eqToHom (by rw [Ctx?.den, h]) := by
  rw [<-ρ.eq_pwk (ety_eq_length_eq h), PWk.den_toWk, PWk.ety_coherence _ h]

theorem Var?.Split.coherence {u v w : Var? α} (σ σ' : u.Split v w)
  : σ.den (C := C) = σ'.den := by
  cases σ <;> cases σ' <;> (
    simp only [
      Ty.den, den_left, den_right, den_neither, den_sboth, Wk.den_unused, eqToHom_refl,
      Category.comp_id
    ]
    first | rw [M.copy_drop_tensor_right]
          | rw [M.copy_drop_tensor_left]
          | rw [M.copy_drop_both (hA := _)]
          | try simp only [MonoidalCategory'.unitors_inv_equal]
  )

theorem Ctx?.Split.coherence {Γ Δ Ξ : Ctx? α} (σ σ' : Γ.Split Δ Ξ)
  : σ.den (C := C) = σ'.den := by
  induction σ <;> cases σ' <;> simp only [den, Iso.cancel_iso_hom_right]; congr 1
  apply_assumption
  apply Var?.Split.coherence

theorem Var?.SSplit.den_unstrict {u v w : Var? α} (σ : u.SSplit v w)
  : σ.unstrict.den = σ.den (C := C) := by cases σ <;> simp

theorem Ctx?.SSplit.den_unstrict {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  : σ.unstrict.den = σ.den (C := C) := by induction σ <;> simp [Var?.SSplit.den_unstrict, *]

theorem Var?.SSplit.coherence {u v w : Var? α} (σ σ' : u.SSplit v w)
  : σ.den (C := C) = σ'.den := by rw [<-σ.den_unstrict, <-σ'.den_unstrict, σ.unstrict.coherence]

theorem Ctx?.SSplit.coherence {Γ Δ Ξ : Ctx? α} (σ σ' : Γ.SSplit Δ Ξ)
  : σ.den (C := C) = σ'.den := by rw [<-σ.den_unstrict, <-σ'.den_unstrict, σ.unstrict.coherence]

theorem Var?.Split.to_zero {u : Var? α} {A B} (σ : u.Split ⟨A, 0⟩ ⟨B, 0⟩)
  : σ.den (C := C) = (haveI _ : u.del := σ.del_in; !_ u.ety) ≫ (λ_ _).inv
  := by cases σ with
  | sboth =>
    simp only [Ty.den, den_sboth, Wk.den_unused, eqToHom_refl, Category.comp_id]
    rw [M.copy_drop_both (hA := _) (hA' := _)]
  | _ => simp only [
    Ty.den, den_neither, den_left, den_right, den_sboth, Wk.den_unused, eqToHom_refl,
    Category.comp_id, unitors_inv_equal
  ]

theorem Var?.Split.from_zero {X Y Z : Ty α} (σ : Split ⟨X, 0⟩ ⟨Y, 0⟩ ⟨Z, 0⟩)
  : σ.den (C := C) = (λ_ _).inv
  := by rw [to_zero, M.drop_unit]; simp only [Ty.den, Category.id_comp]

theorem Var?.Split.den_left_zero {u w : Var? α} (σ : u.Split ⟨X, 0⟩ w)
  : σ.den (C := C) = (Var?.Wk.den σ.wk_left_zero) ≫ (λ_ _).inv
  := by cases σ <;> simp [MonoidalCategory'.unitors_inv_equal, M.copy_drop_tensor_left]

theorem Var?.Split.den_right_zero {u w : Var? α} (σ : u.Split w ⟨X, 0⟩)
  : σ.den (C := C) = (Var?.Wk.den σ.wk_right_zero) ≫ (ρ_ _).inv
  := by cases σ <;> simp [MonoidalCategory'.unitors_inv_equal, M.copy_drop_tensor_right]

theorem Var?.Split.den_both_quant {u : Var? α} {X Y : Ty α} {qX qY : Quant}
  (σ : Split u ⟨X, qX⟩ ⟨Y, qY⟩)
  : σ.den (C := C) =
  (haveI _ := σ.scopy_both.copy; Δ_ _)
    ≫ (σ.wk_left_both.den (C := C) ⊗ σ.wk_right_both.den)
  := by cases σ; rfl

@[reassoc]
theorem Var?.Split.den_braiding {u v w : Var? α} (σ : u.Split v w)
  : σ.den (C := C) ≫ (β'_ _ _).hom = σ.comm.den
  := by cases σ with
  | sboth =>
    simp [
      tensorHom_def, BraidedCategory'.braiding_naturality_left_assoc,
      BraidedCategory'.braiding_naturality_right
    ]
    rw [M.copy_swap_assoc (hA := _), <-tensorHom_def, <-tensorHom_def_of_left]
  | _ => simp [MonoidalCategory'.unitors_inv_equal]

@[reassoc]
theorem Var?.Split.den_braiding_self {u : Var? α} (σ : u.Split u u)
  : σ.den (C := C) ≫ (β'_ _ _).hom = σ.den
  := by rw [den_braiding]; apply coherence

@[reassoc]
theorem Var?.Split.den_braiding_inv {u v w : Var? α} (σ : u.Split v w)
  : σ.den (C := C) ≫ (β'_ _ _).inv = σ.comm.den
  := by
  rw [<-cancel_mono (f := (β'_ _ _).hom), den_braiding]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply coherence

@[reassoc]
theorem Var?.Split.den_braiding_inv_self {u : Var? α} (σ : u.Split u u)
  : σ.den (C := C) ≫ (β'_ _ _).inv = σ.den
  := by rw [den_braiding_inv]; apply coherence

@[reassoc]
theorem Var?.Split.den_wkIn {u' u v w : Var? α} (ρ : u'.Wk u) (σ : u.Split v w)
  : ρ.den (C := C) ≫ σ.den = (σ.wkIn ρ).den
  := by cases v using Var?.casesZero with
  | zero _ => simp [den_left_zero]
  | rest => cases u using Var?.casesZero with
  | zero => cases σ.zero_not_left_quant
  | rest => cases w using Var?.casesZero with
  | zero _ => simp [den_right_zero]
  | rest => cases u' using Var?.casesZero with
  | zero => cases ρ.zero_to_quant
  | rest =>
    cases ρ.ty
    cases σ.ty_eq_left
    cases σ.ty_eq_right
    simp [ety, den_both_quant]

@[reassoc]
theorem Var?.Split.den_wkOutL {u v v' w : Var? α} (σ : u.Split v w) (ρ : v.Wk v')
  : σ.den (C := C) ≫ ρ.den ▷ _ = (σ.wkOutL ρ).den
  := by cases v using Var?.casesZero with
  | zero _ => cases v'; cases ρ; simp [den_left_zero]
  | rest => cases u using Var?.casesZero with
  | zero => cases σ.zero_not_left_quant
  | rest => cases σ.ty_eq_left; cases σ.ty_eq_right; cases w using Var?.casesZero with
  | zero => simp [ety, den_right_zero]; apply Var?.Wk.quant_coherence
  | rest => cases v' using Var?.casesZero with
  | zero =>
    cases ρ.ty; simp [ety, den_left_zero, den_both_quant]
    exact M.copy_drop_left (hA := _) (hA' := _)
  | rest => cases ρ.ty; simp [den_both_quant]

@[reassoc]
theorem Var?.Split.den_wkOutR {u v w w' : Var? α} (σ : u.Split v w) (ρ : w.Wk w')
  : σ.den (C := C) ≫ _ ◁ ρ.den = (σ.wkOutR ρ).den
  := by cases w using Var?.casesZero with
  | zero _ => cases ρ; simp [den_right_zero]
  | rest => cases u using Var?.casesZero with
  | zero => cases σ.zero_not_right_quant
  | rest => cases σ.ty_eq_left; cases σ.ty_eq_right; cases v using Var?.casesZero with
  | zero => simp [ety, den_left_zero]; apply Var?.Wk.quant_coherence
  | rest => cases σ.ty_eq_left; cases σ.ty_eq_right; cases w' using Var?.casesZero with
  | zero =>
    cases ρ.ty; simp [ety, den_right_zero, den_both_quant]
    exact M.copy_drop_right (hA := _) (hA' := _)
  | rest => cases ρ.ty; simp [den_both_quant]

@[reassoc]
theorem Var?.Split.den_wkOut {u v w v' w' : Var? α} (σ : u.Split v w) (ρv : v.Wk v') (ρw : w.Wk w')
  : σ.den (C := C) ≫ (ρv.den ⊗ ρw.den) = (σ.wkOut ρv ρw).den
  := by rw [<-wkOutL_wkOutR, <-den_wkOutR, <-den_wkOutL, Category.assoc, tensorHom_def]

@[reassoc]
theorem Ctx?.Split.den_wkIn {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.PWk Γ) (σ : Γ.Split Δ Ξ)
  : ρ.den (C := C) ≫ σ.den = (σ.wkIn ρ).den
  := by induction σ generalizing Γ' with
  | nil => cases ρ; simp; convert Category.id_comp _
  | cons σ ρ' I =>
    cases ρ; simp [<-tensor_comp_of_left_assoc, I, Var?.Split.den_wkIn, Ctx?.Split.wkIn]

@[reassoc]
theorem Ctx?.Split.den_wkOutL {Γ Δ Δ' Ξ : Ctx? α} (σ : Γ.Split Δ Ξ) (ρ : Δ.PWk Δ')
  : σ.den (C := C) ≫ ρ.den ▷ _ = (σ.wkOutL ρ).den
  := by induction σ generalizing Δ' with
  | nil => cases ρ; simp; convert Category.comp_id _; apply PremonoidalCategory.id_whiskerRight _ _
  | cons σ ρ' I =>
    cases ρ
    simp only [
      den, tensorHom_def, Category.assoc, PWk.den, comp_whiskerRight, wkOutL, Ctx?.den, Ty.den,
      Ctx?.ety,
    ]
    rw [
      <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right,
      Central.left_exchange_assoc, <-PremonoidalCategory.comp_whiskerRight_assoc,
      I, <-Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
      Var?.Split.den_wkOutL
    ]

@[reassoc]
theorem Ctx?.Split.den_wkOutR {Γ Δ Ξ Ξ' : Ctx? α} (σ : Γ.Split Δ Ξ) (ρ : Ξ.PWk Ξ')
  : σ.den (C := C) ≫ _ ◁ ρ.den = (σ.wkOutR ρ).den
  := by induction σ generalizing Ξ' with
  | nil => cases ρ; simp; convert Category.comp_id _; apply PremonoidalCategory.whiskerLeft_id _ _
  | cons σ ρ' I =>
    cases ρ
    simp only [
      den, tensorHom_def, Category.assoc, PWk.den, PremonoidalCategory.whiskerLeft_comp, wkOutR,
      Ctx?.den, Ty.den, Ctx?.ety,
    ]
    rw [
      <-swap_inner_naturality_left_assoc,
      <-swap_inner_naturality_outer_right,
      Central.left_exchange_assoc, <-PremonoidalCategory.comp_whiskerRight_assoc,
      I, <-Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
      Var?.Split.den_wkOutR
    ]

@[reassoc]
theorem Ctx?.Split.den_wkOut {Γ Δ Δ' Ξ Ξ' : Ctx? α}
  (σ : Γ.Split Δ Ξ) (ρΞ : Ξ.PWk Ξ') (ρΔ : Δ.PWk Δ')
  : σ.den (C := C) ≫ (ρΔ.den ⊗ ρΞ.den) = (σ.wkOut ρΔ ρΞ).den
  := by rw [<-wkOutL_wkOutR, <-den_wkOutR, <-den_wkOutL, Category.assoc, tensorHom_def]

@[reassoc]
theorem Var?.Split.assoc_coherence {u₁₂₃ u₁₂ u₂₃ u₁ u₂ u₃ : Var? α}
  (σ123_12_3 : u₁₂₃.Split u₁₂ u₃) (σ12 : u₁₂.Split u₁ u₂)
  (σ123_1_23 : u₁₂₃.Split u₁ u₂₃) (σ23 : u₂₃.Split u₂ u₃)
  : σ123_12_3.den (C := C) ≫ σ12.den ▷ _ ≫ (α_ _ _ _).hom
  = σ123_1_23.den ≫ _ ◁ σ23.den
  := by cases u₁₂₃ with
  | mk X q₁₂₃ => cases u₁₂ with
  | mk X₁₂ q₁₂ => cases u₂₃ with
  | mk X₂₃ q₂₃ => cases u₁ with
  | mk X₁ q₁ => cases u₂ with
  | mk X₂ q₂ => cases u₃ with
  | mk X₃ q₃ =>
    cases σ123_12_3.ty_eq_left
    cases σ123_12_3.ty_eq_right
    cases σ12.ty_eq_left
    cases σ12.ty_eq_right
    cases σ123_1_23.ty_eq_left
    cases σ123_1_23.ty_eq_right
    cases q₃ using EQuant.casesZero with
    | zero =>
      simp [den_right_zero]
      simp [<-Category.assoc]
      cases q₁ using EQuant.casesZero with
      | zero => simp [den_left_zero]
      | rest q₁ => cases q₁₂ using EQuant.casesZero with
      | zero => cases σ12.zero_not_left_quant
      | rest q₁₂ => cases q₂ using EQuant.casesZero with
      | zero => cases q₂₃ using EQuant.casesZero with
        | zero => simp [den_right_zero]
        | rest q₂₃ => cases σ123_1_23 with
        | sboth => cases q₁₂₃ using EQuant.casesZero with
        | zero => cases σ123_12_3.zero_not_left_quant
        | rest q₁₂₃ =>
          simp [den_left_zero, den_right_zero]; rw [M.copy_drop_right (hA := _) (hA' := _)]
      | rest q₂ => cases q₂₃ using EQuant.casesZero with
      | zero => cases σ23.zero_not_left_quant
      | rest q₂₃ =>
        simp [den_both_quant, den_right_zero, den_left_zero]
        rw [M.copy_rel_tensor ⊥ (h := _) (hA := _) (hB := _)]
        infer_instance
    | rest q₃ => cases q₂₃ using EQuant.casesZero with
    | zero => cases σ23.zero_not_right_quant
    | rest q₂₃ => cases q₁₂₃ using EQuant.casesZero with
    | zero => cases σ123_12_3.zero_not_right_quant
    | rest q₁₂₃ => cases q₂ using EQuant.casesZero with
    | zero => cases q₁ using EQuant.casesZero with
      | zero => cases q₁₂ using EQuant.casesZero with
        | zero => simp [den_left_zero]
        | rest q₁₂ =>
          simp [den_left_zero, den_right_zero, den_both_quant]
          rw [M.copy_drop_left_assoc (hA := _) (hA' := _)]
      | rest q₁ => cases q₁₂ using EQuant.casesZero with
      | zero => cases σ12.zero_not_left_quant
      | rest q₁₂ => simp [den_left_zero, den_right_zero, den_both_quant]
    | rest q₂ => cases q₁₂ using EQuant.casesZero with
    | zero => cases σ12.zero_not_right_quant
    | rest q₁₂ => cases q₁ using EQuant.casesZero with
    | zero => simp [den_left_zero, den_both_quant]
    | rest q₁ => simp [den_both_quant]; apply M.copy_assoc (hA := _)

@[reassoc]
theorem Var?.Split.assoc_inv_coherence {u₁₂₃ u₁₂ u₂₃ u₁ u₂ u₃ : Var? α}
  (σ123_12_3 : u₁₂₃.Split u₁₂ u₃) (σ12 : u₁₂.Split u₁ u₂)
  (σ123_1_23 : u₁₂₃.Split u₁ u₂₃) (σ23 : u₂₃.Split u₂ u₃)
  : σ123_1_23.den ≫ _ ◁ σ23.den ≫ (α_ _ _ _).inv
  = σ123_12_3.den (C := C) ≫ σ12.den ▷ _ := by
  rw [<-cancel_mono (f := (α_ _ _ _).hom)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Eq.symm
  apply assoc_coherence

set_option maxHeartbeats 1000000000 in
@[reassoc]
theorem Ctx?.Split.assoc_coherence {Γ₁₂₃ Γ₁₂ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (σ123_12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (σ12 : Γ₁₂.Split Γ₁ Γ₂)
  (σ123_1_23 : Γ₁₂₃.Split Γ₁ Γ₂₃) (σ23 : Γ₂₃.Split Γ₂ Γ₃)
  : σ123_12_3.den (C := C) ≫ σ12.den ▷ _ ≫ (α_ _ _ _).hom
  = σ123_1_23.den ≫ _ ◁ σ23.den
  := by induction Γ₁₂₃ generalizing Γ₁₂ Γ₂₃ Γ₁ Γ₂ Γ₃ with
  | nil => cases σ123_12_3; cases σ123_1_23; cases σ12; cases σ23; simp; premonoidal_coherence
  | cons Γ₁₂₃ v₁₂₃ I => cases σ123_12_3 with
  | cons σ123_12_3 v123_12_3 => cases σ123_1_23 with
  | cons σ123_1_23 v123_1_23 => cases σ12 with
  | cons σ12 v12 => cases σ23 with
  | cons σ23 v23 =>
    rename_i X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    simp only [
      den, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
      tensorHom_def, Ctx?.den, Ty.den, Ctx?.ety,
      <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_left_assoc,
      <-swap_inner_naturality_outer_right_assoc,
    ]
    apply Eq.symm
    rw [
      <-Central.left_exchange_assoc, <-PremonoidalCategory.comp_whiskerRight_assoc,
      <-I σ123_12_3 σ12 σ123_1_23 σ23, <-PremonoidalCategory.whiskerLeft_comp_assoc,
      <-Var?.Split.assoc_coherence v123_12_3 v12 v123_1_23 v23,
      PremonoidalCategory.comp_whiskerRight_assoc
    ]
    congr 1
    rw [PremonoidalCategory.whiskerLeft_comp_assoc, Central.left_exchange_assoc]
    congr 1
    rw [PremonoidalCategory.comp_whiskerRight_assoc]
    congr 1
    rw [
      PremonoidalCategory.whiskerLeft_comp_assoc,
      <-swap_inner_naturality_right_assoc,
      Central.left_exchange_assoc
    ]
    congr 1
    simp only [Ctx?.den, swap_inner, assoc_inner]
    rw [
      <-cancel_epi (f := (α_ _ _ _).hom),
      <-cancel_epi (f := (α_ _ _ _).inv ▷ _),
      <-cancel_epi (f := (α_ _ _ _).inv ▷ _),
      <-cancel_epi (f := (_ ◁ (α_ _ _ _).hom) ▷ _),
      <-cancel_epi (f := (_ ◁ (α_ _ _ _).hom) ▷ _),
      <-cancel_epi (f := (α_ _ _ _).inv),
      <-cancel_mono (f := (α_ _ _ _).hom),
      <-cancel_mono (f := _ ◁ (α_ _ _ _).inv),
      <-cancel_mono (f := _ ◁ (α_ _ _ _).inv),
      <-cancel_mono (f := _ ◁ (α_ _ _ _).hom ▷ _),
    ]
    let L
      : _
      ⟶ (t⟦X6.ety⟧ ⊗ (t⟦X8.ety⟧ ⊗ t⟦X9.ety⟧) ⊗ t⟦X1.ety⟧ : C)
      := (
        (β'_ _ _).hom ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ (α_ _ _ _).hom
        ≫ _ ◁ _ ◁ (β'_ _ _).hom
        ≫ _ ◁ (α_ _ _ _).inv
      )
    let R
      : _
      ⟶ (t⟦X6.ety⟧ ⊗ (t⟦X8.ety⟧ ⊗ t⟦X9.ety⟧) ⊗ t⟦X1.ety⟧ : C)
      := (
        (α_ _ _ _).hom ≫
        (α_ _ _ _).hom ≫
        _ ◁ (β'_ _ _).hom ≫
        (α_ _ _ _).inv ≫
        (α_ _ _ _).inv ▷ _ ≫
        ((β'_ _ _).hom ▷ _) ▷ _ ≫
        (α_ _ _ _).hom ▷ _ ≫
        (α_ _ _ _).hom
      )
    have hLR : L = R := by
      simp only [L, R]
      simp only [BraidedCategory'.braiding_tensor_left, comp_whiskerRight, whisker_assoc,
        Category.assoc, pentagon_assoc, BraidedCategory'.braiding_tensor_right,
        PremonoidalCategory.whiskerLeft_comp, pentagon_inv_assoc,
        pentagon_hom_hom_inv_hom_hom_assoc, R, L]
      congr 3
      rw [
        <-associator_naturality_right_assoc,
        whiskerRight_tensor_symm_assoc,
        Iso.inv_hom_id_assoc,
        Central.left_exchange_assoc
      ]
      premonoidal
    calc
      _ = (_ ◁ L ▷ _) := by premonoidal
      _ = (_ ◁ R ▷ _) := by rw [hLR]
      _ = _ := by premonoidal

theorem Ctx?.SSplit.den_both {Γ : Ctx? α} [hΓ : Γ.copy]
  : Γ.both.den (C := C) = Δ_ _ := by
  generalize hΓ = hΓ
  induction Γ with
  | nil => simp only [both, den.eq_1, ety, Model.copy_unit, Ty.den]; rfl
  | cons Γ v I =>
    have _ := hΓ.head;
    have _ := hΓ.tail;
    rw [both_cons]
    simp only [den, ety, I, Var?.SSplit.both]
    rw [M.copy_tensor]
    cases v using Var?.casesZero with
    | zero A => simp [Var?.ety, MonoidalCategory'.unitors_inv_equal]
    | rest A q => simp

@[reassoc]
theorem Ctx?.Split.assoc_inv_coherence {Γ₁₂₃ Γ₁₂ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (σ123_12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (σ12 : Γ₁₂.Split Γ₁ Γ₂)
  (σ123_1_23 : Γ₁₂₃.Split Γ₁ Γ₂₃) (σ23 : Γ₂₃.Split Γ₂ Γ₃)
  : σ123_12_3.den (C := C) ≫ σ12.den ▷ _
  = σ123_1_23.den ≫ _ ◁ σ23.den ≫ (α_ _ _ _).inv
  := by rw [<-Ctx?.Split.assoc_coherence_assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
theorem Ctx?.SSplit.assoc_coherence {Γ₁₂₃ Γ₁₂ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (σ123_12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) (σ12 : Γ₁₂.SSplit Γ₁ Γ₂)
  (σ123_1_23 : Γ₁₂₃.SSplit Γ₁ Γ₂₃) (σ23 : Γ₂₃.SSplit Γ₂ Γ₃)
  : σ123_12_3.den (C := C) ≫ σ12.den ▷ _ ≫ (α_ _ _ _).hom
  = σ123_1_23.den ≫ _ ◁ σ23.den
  := by simp only [<-Ctx?.SSplit.den_unstrict]; apply Ctx?.Split.assoc_coherence

@[reassoc]
theorem Ctx?.SSplit.assoc_inv_coherence {Γ₁₂₃ Γ₁₂ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (σ123_12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) (σ12 : Γ₁₂.SSplit Γ₁ Γ₂)
  (σ123_1_23 : Γ₁₂₃.SSplit Γ₁ Γ₂₃) (σ23 : Γ₂₃.SSplit Γ₂ Γ₃)
  : σ123_12_3.den (C := C) ≫ σ12.den ▷ _
  = σ123_1_23.den ≫ _ ◁ σ23.den ≫ (α_ _ _ _).inv
  := by simp only [<-Ctx?.SSplit.den_unstrict]; apply Ctx?.Split.assoc_inv_coherence

@[reassoc]
theorem Ctx?.SSplit.den_dup_left_dup_eq_wk {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  [hΓ : Γ.copy] [hΞ : Ξ.del]
  : σ.den (C := C) ≫ (haveI _ : Δ.copy := σ.left_copy; Δ_ Δ.ety) ▷ _
  = Δ_ Γ.ety ≫ (σ.pwk_right_del.den (C := C) ⊗ σ.den) ≫ (α_ _ _ _).inv := by
  rw [tensorHom_def]
  haveI _ : Δ.copy := σ.left_copy
  simp only [
    <-Ctx?.SSplit.den_both, <-Ctx?.SSplit.den_unstrict, Category.assoc, Ctx?.Split.den_wkOutL_assoc
  ]
  apply Ctx?.Split.assoc_inv_coherence

@[reassoc]
theorem Var?.SSplit.den_drop_right {u v w : Var? α} (σ : u.SSplit v w)
  [hΞ : w.del] : σ.den (C := C) ≫ _ ◁ !_ w.ety = σ.wk_right_del.den (C := C) ≫ (ρ_ _).inv
  := by cases σ <;> simp [MonoidalCategory'.unitors_inv_equal]; apply M.copy_drop_right (hA := _)

@[reassoc]
theorem Ctx?.SSplit.den_drop_right {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  [hΞ : Ξ.del] : σ.den (C := C) ≫ _ ◁ !_ Ξ.ety = σ.pwk_right_del.den (C := C) ≫ (ρ_ _).inv
  := by
  generalize hΞ = hΞ
  induction σ with
  | nil => simp only [den, ety, Model.drop_unit, pwk_right_del, PWk.den]; premonoidal_coherence
  | cons σΓ σv I =>
    simp only [cons_del_iff] at hΞ
    cases hΞ
    simp only [Ctx?.den, ety, Ty.den, den, tensorHom_def, Category.assoc,
      M.drop_tensor, id_whiskerLeft, Iso.inv_hom_id, Category.comp_id,
      PremonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_assoc,
      <-swap_inner_naturality_left_assoc, swap_inner_tensorUnit_left,
    ]
    rw [
      Central.left_exchange_assoc, <-PremonoidalCategory.comp_whiskerRight_assoc, I,
      <-PremonoidalCategory.comp_whiskerRight_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, PremonoidalCategory.whiskerLeft_inv_hom_assoc,
      <-associator_inv_naturality_right, Central.left_exchange_assoc,
      <-PremonoidalCategory.whiskerLeft_comp_assoc, Var?.SSplit.den_drop_right,
      <-Central.left_exchange_assoc, SSplit.pwk_right_del, PWk.den, tensorHom_def,
    ]
    simp
    infer_instance

@[reassoc]
theorem Ctx?.SSplit.den_pwk_right_del {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  [hΞ : Ξ.del] : σ.pwk_right_del.den (C := C) = σ.den ≫ _ ◁ !_ Ξ.ety ≫ (ρ_ _).hom
  := by rw [<-cancel_mono (f := (ρ_ _).inv)]; simp [den_drop_right]

@[reassoc]
theorem Ctx?.SSplit.den_drop_tensor_right {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) {X : C} (f : g⟦Δ⟧ ⟶ X)
  [hΞ : Ξ.del]
  : σ.den (C := C) ≫ (f ⊗ !_ Ξ.ety) = σ.pwk_right_del.den (C := C) ≫ f ≫ (ρ_ _).inv
  := by rw [den_pwk_right_del, tensorHom_def_of_right]; premonoidal

@[reassoc]
theorem Var?.SSplit.den_drop_left {u v w : Var? α} (σ : u.SSplit v w)
  [hΞ : v.del] : σ.den (C := C) ≫ !_ v.ety ▷ _ = σ.wk_left_del.den (C := C) ≫ (λ_ _).inv
  := by cases σ <;> simp [MonoidalCategory'.unitors_inv_equal]; apply M.copy_drop_left (hA := _)

@[reassoc]
theorem Ctx?.SSplit.den_drop_left {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  [hΔ : Δ.del] : σ.den (C := C) ≫ !_ Δ.ety ▷ _ = σ.pwk_left_del.den (C := C) ≫ (λ_ _).inv
  := by
  generalize hΔ = hΔ
  induction σ with
  | nil => simp only [den, ety, Model.drop_unit, pwk_left_del, PWk.den]; premonoidal_coherence
  | cons σΓ σv I =>
    simp only [cons_del_iff] at hΔ
    cases hΔ
    simp only [Ctx?.den, ety, Ty.den, den, tensorHom_def, Category.assoc,
      M.drop_tensor, id_whiskerLeft, Iso.inv_hom_id, Category.comp_id,
      comp_whiskerRight, leftUnitor_whiskerRight, <-swap_inner_naturality_outer_left_assoc]
    rw [
      Central.left_exchange_assoc, <-PremonoidalCategory.comp_whiskerRight_assoc, I,
      <-leftUnitor_naturality, <-associator_naturality_middle_assoc,
      <-swap_inner_naturality_right_assoc, swap_inner_tensorUnit_right,
      <-Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
      Var?.SSplit.den_drop_left
    ]
    simp only [SSplit.pwk_left_del, PWk.den, tensorHom_def]
    simp only [comp_whiskerRight, leftUnitor_inv_whiskerRight, PremonoidalCategory.whiskerLeft_comp,
      tensor_whiskerLeft, id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, whiskerRight_tensor,
      whiskerLeft_inv_hom_assoc]
    congr 2
    premonoidal_coherence

@[reassoc]
theorem Ctx?.SSplit.den_pwk_left_del {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  [hΔ : Δ.del] : σ.pwk_left_del.den (C := C) = σ.den ≫ !_ Δ.ety ▷ _ ≫ (λ_ _).hom
  := by rw [<-cancel_mono (f := (λ_ _).inv)]; simp [den_drop_left]

@[reassoc]
theorem Ctx?.SSplit.den_drop_tensor_left {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) {X : C} (f : g⟦Ξ⟧ ⟶ X)
  [hΔ : Δ.del]
  : σ.den (C := C) ≫ (!_ Δ.ety ⊗ f) = σ.pwk_left_del.den (C := C) ≫ f ≫ (λ_ _).inv
  := by rw [den_pwk_left_del, tensorHom_def]; premonoidal

@[reassoc]
theorem Ctx?.SSplit.den_s12_3_1_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (σ12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) (σ12 : Γ₁₂.SSplit Γ₁ Γ₂)
  : (σ12_3.s12_3_1_23 σ12).den (C := C) ≫ _ ◁ (σ12_3.s12_3_23 σ12).den
  = σ12_3.den (C := C) ≫ σ12.den ▷ _ ≫ (α_ _ _ _).hom
  := by rw [assoc_coherence]

@[reassoc]
theorem Ctx?.SSplit.den_s1_23_12_3 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (σ1_23 : Γ₁₂₃.SSplit Γ₁ Γ₂₃) (σ23 : Γ₂₃.SSplit Γ₂ Γ₃)
  : (σ1_23.s1_23_12_3 σ23).den (C := C) ≫ (σ1_23.s1_23_12 σ23).den ▷ _
  = σ1_23.den (C := C) ≫ _ ◁ σ23.den ≫ (α_ _ _ _).inv
  := by rw [assoc_inv_coherence]

end Braided

section Symmetric

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [ChosenFiniteCoproducts C]
         [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε]
         [M : Model φ α ε C]

theorem Ctx?.Split.den_braiding {Γ Δ Ξ : Ctx? α} (σ : Γ.Split Δ Ξ)
  : σ.den (C := C) ≫ (β'_ _ _).hom = σ.comm.den
  := by induction σ with
  | nil => simp [Ctx?.den]; premonoidal_coherence
  | cons σ σv I =>
    calc
      _ = (σ.den (C := C) ⊗ σv.den)
        ≫ (βi_ _ _ _ _).hom
        ≫ (βi_ _ _ _ _).hom
        ≫ (β'_ _ _).hom ▷ _
        ≫ _ ◁ (β'_ _ _).hom
        ≫ (βi_ _ _ _ _).hom
        := by
          simp only [
            den, Category.assoc, tensorHom_def, assoc_inner, swap_inner, Ctx?.den, Ctx?.ety, Ty.den,
            BraidedCategory'.braiding_tensor_left, BraidedCategory'.braiding_tensor_right,
          ]
          premonoidal
      _ = (σ.comm.den (C := C) ⊗ σv.comm.den)
        ≫ (βi_ _ _ _ _).hom
        := by
        simp only [
          MonoidalCategory'.swap_inner_swap_inner_assoc, tensorHom_def_of_left, Category.assoc,
          <-PremonoidalCategory.comp_whiskerRight_assoc, I
        ]
        rw [
          Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc,
          Var?.Split.den_braiding
        ]

theorem Ctx?.SSplit.den_braiding {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  : σ.den (C := C) ≫ (β'_ _ _).hom = σ.comm.den
  := by
  rw [<-Ctx?.SSplit.den_unstrict, Ctx?.Split.den_braiding, <-Ctx?.SSplit.den_unstrict]
  apply Ctx?.Split.coherence

theorem Ctx?.SSplit.den_comm {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ)
  : σ.comm.den (C := C) = σ.den ≫ (β'_ _ _).hom
  := by rw [den_braiding]

@[reassoc]
theorem Ctx?.SSplit.den_s12_34_13_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx? α}
  (σ12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (σ12 : Γ₁₂.SSplit Γ₁ Γ₂) (σ34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : (σ12_34.s12_34_13_24 σ12 σ34).den (C := C)
    ≫ ((σ12_34.s12_34_13 σ12 σ34).den ⊗ (σ12_34.s12_34_24 σ12 σ34).den)
  = σ12_34.den ≫ (σ12.den (C := C) ⊗ σ34.den) ≫ (βi_ _ _ _ _).hom
  := by
  rw [tensorHom_def, tensorHom_def_of_left]
  simp only [
    s12_34_13_24, s12_34_13, s12_34_24, s12_34_12_3, s12_34_123_4, s12_3_31,
    Category.assoc, den_comm, s12_34_13_2, s1_23_13_2
  ]
  rw [
    left_exchange, den_s12_3_1_23_assoc, s12_3_13_2, <-associator_naturality_left,
    <-comp_whiskerRight_assoc (Z := g⟦Γ₄⟧), comp_whiskerRight (Z := g⟦Γ₂⟧),
    den_s1_23_12_3_assoc, den_comm, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    den_s1_23_12_3_assoc, <-comp_whiskerRight_assoc (Z := g⟦Γ₄⟧),
    <-BraidedCategory'.braiding_naturality_left_assoc, BraidedCategory'.braiding_tensor_left_assoc,
    Iso.hom_inv_id_assoc, <-comp_whiskerRight (Z := g⟦Γ₂⟧), SymmetricCategory'.symmetry,
    id_whiskerRight, Category.comp_id
  ]
  simp only [swap_inner, assoc_inner]
  premonoidal
