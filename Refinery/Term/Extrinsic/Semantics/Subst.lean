import Refinery.Term.Extrinsic.Subst.Effect
import Refinery.Ctx.Semantics.Coherence
import Refinery.Term.Extrinsic.Semantics.Typing

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open ChosenFiniteCoproducts

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

def Deriv?.den {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} : (Γ ⊢? a : v) → ((g⟦Γ⟧ : C) ⟶ v⟦v⟧)
  | .valid _ _ D hΓ => D.den
  | .zero hΓ a A => !_ _

def SubstDS.den {Γ Δ : Ctx? α} : (σ : SubstDS φ Γ Δ) → ((g⟦Γ⟧ : C) ⟶ g⟦Δ⟧)
  | .nil hΓ => !_ _
  | .cons hΓ σ da => hΓ.den ≫ (σ.den ⊗ da.den)

-- TODO: den pre-effect

-- TODO: den_bv0

-- TODO: den_lift

-- TODO: den_ssplit

-- TODO: den_at

-- TODO: semantic substitution!
