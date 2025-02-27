import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Semantics.Typing

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open HasCommRel

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

class RWS.Valid (R : RWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]
  : Prop where
  den_eq {Γ A a b} (h : R Γ A a b) (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) = Db.den

instance RWS.instValidBot : Valid (φ := φ) ⊥ C where den_eq h := h.elim

-- TODO: Requires coherence!
-- theorem RWS.uniform.eq {R : RWS φ α} [R.Valid C] {Γ A a b} (h : uniform R Γ A a b)
--   (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) = Db.den := sorry
