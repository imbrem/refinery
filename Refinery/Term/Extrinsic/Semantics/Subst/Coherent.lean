import Refinery.Term.Extrinsic.Semantics.Subst
import Refinery.Term.Extrinsic.Semantics.Minimal

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

theorem Deriv.den_subst_pos' {eσ ea : ε} (he : eσ ⇀ ea)
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos eσ] {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) [ha : a.HasEff ea] (Dσ : Γ ⊢ a.subst σ : A) : σ.den ≫ D.den ↠ Dσ.den (C := C)
  := by convert D.den_subst_pos he σ using 1; apply Deriv.coherence

theorem Deriv.den_subst_neg' {eσ ea : ε} (he : eσ ↽ ea)
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg eσ] {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) [ha : a.HasEff ea] (Dσ : Γ ⊢ a.subst σ : A) : σ.den ≫ D.den ↞ Dσ.den (C := C)
  := by convert D.den_subst_neg he σ using 1; apply Deriv.coherence
