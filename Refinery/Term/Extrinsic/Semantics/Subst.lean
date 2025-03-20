import Refinery.Term.Extrinsic.Subst.Effect
import Refinery.Term.Extrinsic.Semantics.Wk
import Refinery.Term.Extrinsic.Semantics.Effect
import Refinery.Ctx.Semantics.SplitWk
import Refinery.Ctx.Semantics.Coherence

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open ChosenFiniteCoproducts

open HasQuant

open HasCommRel

namespace Term

section BraidedCategory

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

def Deriv?.den {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} : (Γ ⊢? a : v) → ((g⟦Γ⟧ : C) ⟶ v⟦v⟧)
  | .valid _ _ D hΓ => D.den
  | .zero hΓ a A => !_ _

@[simp]
theorem Deriv?.den_valid {Γ : Ctx? α} {A : Ty α} {q : Quant} {a : Term φ (Ty α)} (D : Γ ⊢ a : A)
  (hΓ : quant (Var?.mk A q) ≤ quant Γ)
  : (Deriv?.valid A q D hΓ).den (C := C) = D.den
  := rfl

@[simp]
theorem Deriv?.den_zero {Γ : Ctx? α} [hΓ : Γ.del] {a : Term φ (Ty α)} {A : Ty α}
  : (Deriv?.zero hΓ a A).den (C := C) = !_ _
  := rfl

@[simp]
instance Deriv?.den_eff (e : ε) {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (D : Γ ⊢? a : v)
  [hD : D.HasEff e]
  : E.HasEff e D.den := by cases hD <;> simp only [Deriv?.den] <;> infer_instance

def SubstDS.den {Γ Δ : Ctx? α} : (σ : SubstDS φ Γ Δ) → ((g⟦Γ⟧ : C) ⟶ g⟦Δ⟧)
  | .nil hΓ => !_ _
  | .cons hΓ σ da => hΓ.den ≫ (σ.den ⊗ da.den)

@[simp]
instance SubstDS.den_eff (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff e]
  : E.HasEff e σ.den := by induction hσ <;> simp only [SubstDS.den] <;> infer_instance

@[simp]
theorem Deriv?.den_bv0 (Γ : Ctx? α) (v : Var? α)
  : (Deriv?.bv0 Γ v).den (C := C) = !_ Γ.erase.ety ▷ _ ≫ (λ_ _).hom
  := by cases v using Var?.casesZero <;> simp [Deriv?.bv0, Deriv?.den, M.drop_tensor]

theorem Deriv?.den_wk {Γ Δ : Ctx? α}
  (ρ : Γ.Wk Δ) (h : quant Δ ≤ quant Γ) {v : Var? α} (D : Δ ⊢? a : v)
  : (D.wk ρ h).den (C := C) = ρ.den ≫ D.den
  := by cases D <;> simp [Deriv?.den, Deriv?.wk, Deriv.den_wk]

@[reassoc]
theorem SubstDS.den_wkIn {Γ' Γ Δ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : SubstDS φ Γ Δ)
  : (σ.wkIn ρ).den (C := C) = ρ.den ≫ σ.den
  := by induction σ generalizing Γ' with
  | nil => simp [wkIn, den]
  | cons =>
    simp only [wkIn, den, Deriv?.den_wk, tensorHom_def, comp_whiskerRight,
      PremonoidalCategory.whiskerLeft_comp, Category.assoc, Central.right_exchange_assoc, *]
    rw [<-tensorHom_def_of_left_assoc, <-Ctx?.SSplit.wk_den'_assoc]

theorem SubstDS.den_lift {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v : Var? α)
  : (σ.lift v).den (C := C) = σ.den ▷ _
  := by
  simp only [
    lift, den, Deriv?.den_bv0, tensorHom_def_of_right, den_wkIn, Ctx?.Wk.den, Ctx?.wk0,
    Ctx?.Wk.den_refl, id_whiskerRight, Category.comp_id,
    Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
    swap_inner_tensorUnit_right,
    PremonoidalCategory.whiskerLeft_comp, Var?.del.den_unused, eqToHom_refl,
    PremonoidalCategory.whiskerLeft_id, Category.assoc, comp_whiskerRight
  ]
  calc
      _ = (css⟦Γ.erase_right⟧ ≫ _ ◁ !_ Γ.erase.ety ≫ (ρ_ _).hom) ▷ _ ≫ σ.den ▷ _
        := by premonoidal
      _ = _
        := by rw [Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl']; simp

def SubstSSplit.den {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : (g⟦Γ⟧ : C) ⟶ g⟦Δl⟧ ⊗ g⟦Δr⟧
  := σ.ssplitIn.den ≫ (σ.substLeft.den ⊗ σ.substRight.den)

theorem SubstSSplit.den_eq_ltimes {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : σ.den (C := C) = σ.ssplitIn.den ≫ σ.substLeft.den ▷ _ ≫ _ ◁ σ.substRight.den
  := by simp [den, tensorHom_def]

end BraidedCategory

section SymmetricCategory

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

--TODO: need validity here to commute `da` with the subst components...
theorem SubstDS.den_ssplit {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) {e : ε} [hσ : σ.IsValid e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).den (C := C) = σ.den ≫ hΔ.den
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      ssplit, SubstSSplit.erase_left, SubstSSplit.den, den, tensorHom_def,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl'
    ]
    rw [leftUnitor_inv_naturality]; rfl
  | cons hΓ σ da hσ ha hl hr hcomm Iσ => cases hΔ with
  | cons hΔ hlr =>
  simp only [den, tensorHom_def, Category.assoc, Ctx?.SSplit.den]
  rw [<-Central.left_exchange_assoc, <-comp_whiskerRight_assoc, <-Iσ]
  cases hlr with
  | left =>
    simp only [ssplit, ge_iff_le, Deriv?.unused, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_left,
      Category.assoc]
    split
    case isTrue h =>
      stop
      simp only [SubstSSplit.den, den, tensorHom_def, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc, <-Ctx?.SSplit.den_comm,
        <-BraidedCategory'.braiding_naturality_right_assoc
      ]
      rw [
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn.comm)
      ]
      congr 1
      simp only [← Ctx?.SSplit.den_comm, comp_whiskerRight,
        BraidedCategory'.braiding_naturality_right_assoc, BraidedCategory'.braiding_tensor_right,
        Category.assoc, Iso.inv_hom_id_assoc, Deriv?.den_zero, Iso.hom_inv_id_assoc,
        associator_inv_naturality_middle_assoc]
      rw [Central.right_exchange_assoc, (E.eff_comm hcomm).left_exchange_assoc]
      · {
        calc
          _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
            ≫ ((β'_ _ _).hom
              ≫ (_ ◁ (σ.ssplit hΔ).substLeft.den)
              ≫ (β'_ _ _).hom) ▷ _
            ≫ (α_ _ _ _).hom
            ≫ _ ◁ (β'_ _ _).hom
            ≫ (α_ _ _ _).inv
            ≫ _ ◁ (css⟦(σ.ssplit hΔ).inRight.erase_right⟧
              ≫ _ ◁ !_ (σ.ssplit hΔ).inRight.erase.ety)
            ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ▷ _
            ≫ (_ ◁ da.den) ▷ _ := by
              rw [right_exchange (g := _ ◁ !_ _)]
              simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
              rw [<-right_exchange (g := !_ _)]
              premonoidal
          _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
            ≫ (σ.ssplit hΔ).substLeft.den ▷ _ ▷ _
            ≫ (α_ _ _ _).hom
            ≫ _ ◁ ((β'_ _ _).hom ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ≫ da.den ▷ _)
            ≫ (α_ _ _ _).inv
            ≫ _ ◁ (ρ_ _).inv := by
              simp only [
                BraidedCategory'.braiding_naturality_right, SymmetricCategory'.symmetry_assoc,
                Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl', Category.id_comp
              ]
              premonoidal
          _ = _ := by
            congr 2
            rw [
              <-BraidedCategory'.braiding_naturality_left_assoc,
              <-BraidedCategory'.braiding_naturality_right,
            ]
            simp only [swap_inner, assoc_inner]
            premonoidal
      }
      · sorry
      · sorry
    case isFalse h =>
      sorry
  | right => sorry
  | sboth => sorry

-- TODO: den_bv0

-- TODO: den_lift

-- TODO: den_ssplit

-- TODO: den_at

-- TODO: semantic substitution!
