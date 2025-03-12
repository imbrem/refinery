import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Semantics.Minimal
import Refinery.Term.Extrinsic.Semantics.Effect

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open ChosenFiniteCoproducts

open scoped MonoidalCategory

open HasCommRel

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

class RWS.Valid (R : RWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
  : Prop where
  den_ref (h : R Γ A a b) (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) ↠ Db.den

instance RWS.instValidBot : Valid (φ := φ) ⊥ C where den_ref h := h.elim

class RWS.AntiValid (R : RWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
  : Prop where
  den_ref_anti (h : R Γ A a b) (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) ↞ Db.den

instance RWS.instAntiValidBot : AntiValid (φ := φ) ⊥ C where den_ref_anti h := h.elim

instance RWS.swap_anti_valid (R : RWS φ α) [h : Valid R C] : AntiValid R.swap C where
  den_ref_anti h Da Db := Valid.den_ref h.get Db Da

instance RWS.swap_valid (R : RWS φ α) [h : AntiValid R C] : Valid R.swap C where
  den_ref h Da Db := AntiValid.den_ref_anti h.get Db Da

class RWS.BiValid (R : RWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
  : Prop extends AntiValid R C, Valid R C where
  den_eq {Γ A a b} (h : R Γ A a b) (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) = Db.den
    := refines_antisymm (den_ref h Da Db) (den_ref_anti h Da Db)
  den_ref h Da Db := refines_of_eq (den_eq h Da Db)
  den_ref_anti h Da Db := refines_of_eq (den_eq h Da Db).symm

instance RWS.instBivalidBot : BiValid (⊥ : RWS φ α) C where

instance RWS.swap_bivalid (R : RWS φ α) [V : R.BiValid C] : R.swap.BiValid C where

instance RWS.symm_bivalid (R : RWS φ α) [V : R.BiValid C] : R.symm.BiValid C where
  den_ref h Da Db := match h with
    | .fwd h => Valid.den_ref h Da Db
    | .bwd h => AntiValid.den_ref_anti h Db Da
  den_ref_anti h Da Db := match h with
    | .fwd h => AntiValid.den_ref_anti h Da Db
    | .bwd h => Valid.den_ref h Db Da

-- Note: uniform does _not_ preserve bivalidity unless all forward commutative effects are also
-- backward commutative!

instance RWS.iso_bivalid (R : RWS φ α) [V : R.Valid C] : R.iso.BiValid C where
  den_ref h Da Db := Valid.den_ref h.fwd Da Db
  den_ref_anti h Da Db := Valid.den_ref h.bwd Db Da

class DRWS.Valid (R : DRWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
  : Prop where
  den_ref (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) (h : R.rel Da Db) : Da.den (C := C) ↠ Db.den

class DRWS.AntiValid (R : DRWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
  : Prop where
  den_ref_anti (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) (h : R.rel Da Db) : Da.den (C := C) ↞ Db.den

class DRWS.BiValid (R : DRWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
  : Prop extends AntiValid R C, Valid R C where
  den_eq {Γ A a b} (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) (h : R.rel Da Db) : Da.den (C := C) = Db.den
    := refines_antisymm (den_ref Da Db h) (den_ref_anti Da Db h)
  den_ref h Da Db := refines_of_eq (den_eq h Da Db)
  den_ref_anti h Da Db := refines_of_eq (den_eq h Da Db).symm
