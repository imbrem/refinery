import Refinery.Term.Extrinsic.Semantics.Typing
import Refinery.Term.Extrinsic.Effect

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open ChosenFiniteCoproducts

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

namespace Term

instance Deriv.instHasEff {e : ε} {Γ : Ctx? α} {a : Term φ (Ty α)} {A : Ty α}
  (D : Γ ⊢ a : A) [ha : HasEff e a] : E.HasEff e D.den := by
  generalize ha = ha
  induction D with
  | iter =>
    simp [den] at *
    casesm* _ ∧ _
    simp [*] at *
    apply EffectfulCategory.HasEff.comp _ _ (hg := _)
    apply EffectfulCategory.HasEff.comp _ _ (hg := _)
    apply EffectfulCategory.HasEff.iterate _ (by assumption)
  | _ =>
    simp [den] at *
    (try casesm* _ ∧ _)
    (try simp [*] at *)
    infer_instance
