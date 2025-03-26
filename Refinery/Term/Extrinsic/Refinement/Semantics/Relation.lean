import Refinery.Term.Extrinsic.Refinement.Semantics.LetBind
import Refinery.Term.Extrinsic.Refinement.Semantics.LetMove
import Refinery.Term.Extrinsic.Refinement.Semantics.Step
import Refinery.Term.Extrinsic.Refinement.Semantics.Beta
import Refinery.Term.Extrinsic.Refinement.Semantics.Uniform
import Refinery.Term.Extrinsic.Refinement.Relation

namespace Refinery

open CategoryTheory MonoidalCategory' PremonoidalCategory DistributiveCategory
     ChosenFiniteCoproducts

open scoped MonoidalCategory

open HasCommRel HasQuant

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

instance DRWS.EquivFwdStep.bivalid : BiValid (EquivFwdStep (S := S)) C where
  den_eq da db h := by cases h <;> apply BiValid.den_eq _ _ (by assumption)

instance DRWS.EquivStep.bivalid : BiValid (EquivStep (S := S)) C := DRWS.symm_bivalid _

instance DRWS.refStep.valid (R : DRWS φ α) [Valid R C] : Valid R.refStep C where
  den_ref da db h := by cases h <;> apply Valid.den_ref _ _ (by assumption)

instance DRWS.refines.valid (R : DRWS φ α) [Valid R C] : Valid R.refines C := DRWS.uniform_valid _

--TODO: RWS.refStep.valid
