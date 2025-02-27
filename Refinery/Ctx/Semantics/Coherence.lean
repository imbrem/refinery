import Refinery.Ctx.Semantics

namespace Refinery

open CategoryTheory

open PremonoidalCategory MonoidalCategory'

open scoped MonoidalCategory

open EffectfulCategory

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

-- theorem Var?.Split.to_zero {u : Var? α} {A B} (σ : u.Split ⟨A, 0⟩ ⟨B, 0⟩)
--   : σ.den (C := C) = (haveI _ : u.del := σ.del_in; !_ u.ety) ≫ (λ_ _).inv
--   := sorry

-- theorem Var?.Split.assoc_coherence {u₁₂₃ u₁₂ u₂₃ u₁ u₂ u₃ : Var? α}
--   (σ123_12_3 : u₁₂₃.Split u₁₂ u₃) (σ12 : u₁₂.Split u₁ u₂)
--   (σ123_1_23 : u₁₂₃.Split u₁ u₂₃) (σ23 : u₂₃.Split u₂ u₃)
--   : σ123_12_3.den (C := C) ≫ σ12.den ▷ _ ≫ (α_ _ _ _).hom
--   = σ123_1_23.den ≫ _ ◁ σ23.den
--   := by cases σ123_12_3 with
--   | neither => sorry
--   | _ => sorry
