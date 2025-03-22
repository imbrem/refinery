import Refinery.Term.Extrinsic.Semantics.Subst.Basic
import Refinery.Term.Extrinsic.Semantics.Subst.DropAt
import Refinery.Term.Extrinsic.Semantics.Subst.SplitLeft
import Refinery.Term.Extrinsic.Semantics.Subst.SplitRight
--TODO: eventually, split comm is not necessary, via split right?
import Refinery.Term.Extrinsic.Semantics.Subst.SplitComm

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

--TODO: semantic substitution
