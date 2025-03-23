import Refinery.Term.Extrinsic.Subst.Effect
import Refinery.Term.Extrinsic.Semantics.Wk
import Refinery.Term.Extrinsic.Semantics.Effect
import Refinery.Ctx.Semantics.SplitWk
import Refinery.Ctx.Semantics.Coherence

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PC : PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

def Deriv?.den {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} : (Γ ⊢? a : v) → ((g⟦Γ⟧ : C) ⟶ v⟦v⟧)
  | .valid _ _ D hΓ => D.den
  | .zero hΓ a A => !_ _

@[simp]
theorem Deriv?.den_valid {Γ : Ctx? α} {A : Ty α} {q : Quant} {a : Term φ (Ty α)} (D : Γ ⊢ a : A)
  (hΓ : quant (Var?.mk A q) ≤ quant Γ)
  : (Deriv?.valid A q D hΓ).den (C := C) = D.den
  := rfl

theorem Deriv?.den_zero {Γ : Ctx? α} [hΓ : Γ.del] {a : Term φ (Ty α)} {A : Ty α}
  : (Deriv?.zero hΓ a A).den (C := C) = !_ _
  := rfl

@[simp]
theorem Deriv?.den_zero' {Γ : Ctx? α} {a : Term φ (Ty α)} {A : Ty α}
  (da : Γ ⊢? a : ⟨A, 0⟩) : da.den (C := C) = haveI _ : Γ.del := da.del_of_unused (by simp); !_ _
  := by cases da; rfl

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

@[simp]
theorem SubstDS.den_refl (Γ : Ctx? α) : (SubstDS.refl Γ).den (S := S) (C := C) = 𝟙 _
  := by induction Γ <;> simp [refl, den, den_lift, *] <;> rfl

def SubstSSplit.den {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : (g⟦Γ⟧ : C) ⟶ g⟦Δl⟧ ⊗ g⟦Δr⟧
  := σ.ssplitIn.den ≫ (σ.substLeft.den ⊗ σ.substRight.den)

theorem SubstSSplit.den_eq_ltimes {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : σ.den (C := C) = σ.ssplitIn.den ≫ σ.substLeft.den ▷ _ ≫ _ ◁ σ.substRight.den
  := by simp [den, tensorHom_def]

def SubstSSplit.den' {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : (g⟦Γ⟧ : C) ⟶ g⟦Δl⟧ ⊗ g⟦Δr⟧
  := σ.ssplitIn.den ≫ _ ◁ σ.substRight.den ≫ σ.substLeft.den ▷ _

def SubstSSplit.den_left {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  := σ.substLeft.den (C := C) ▷ _ ≫ _ ◁ σ.substRight.den

def SubstSSplit.den_right {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  := _ ◁ σ.substRight.den (C := C) ≫ σ.substLeft.den ▷ _
