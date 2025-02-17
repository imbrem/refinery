import Discretion.Poset2.Elgot
import Discretion.Premonoidal.BraidedHelpers

import Refinery.Signature

namespace Refinery

open CategoryTheory

open Monoidal

open MonoidalCategory

open ChosenFiniteCoproducts

class TyModel
  (α : Type _) [HasQuant α]
  (C : Type _) [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
  where
  den_base : α → C

open TyModel

section TyModel

variable {α : Type _} [HasQuant α]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
        [TyModel α C]

def Ty.den : Ty α → C
  | .of A => TyModel.den_base A
  | .unit => 𝟙_ C
  | .tensor A B => den A ⊗ den B
  | .empty => 𝟘_ C
  | .coprod A B => den A ⊕ₒ den B

notation "t⟦" A "⟧" => Ty.den A

end TyModel

class VarModel
  (α : Type _) [HasQuant α]
  (C : Type _) [Category C] [MC : MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
  extends TyModel α C where
  drop (A : Ty α) [IsAff A] : t⟦ A ⟧ ⟶ 𝟙_ C
  copy (A : Ty α) [IsRel A] : (t⟦ A ⟧ : C) ⟶ t⟦ A ⟧ ⊗ t⟦ A ⟧

notation "!_" => VarModel.drop

notation "Δ_" => VarModel.copy

class SigModel
  (φ : Type _) (α : Type _) (ε : Type _) [S : Signature φ α ε]
  (C : Type _) [Category C] [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
               [BraidedCategoryStruct C] [E : Effectful2 C ε]
  extends VarModel α C
  where
  den_inst (f : φ) : (t⟦S.src f⟧ : C) ⟶ t⟦S.trg f⟧
  den_eff (f : φ) : E.eff (S.eff f) (den_inst f)

notation "i⟦" f "⟧" => SigModel.den_inst f

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
        [BraidedCategoryStruct C]

def Signature.IsFn.den [Effectful2 C ε] [SigModel φ α ε C]
  {f : φ} {e : ε} {A B : Ty α} (h : IsFn f e A B)
  : (t⟦ A ⟧ : C) ⟶ t⟦ B ⟧ := eq_hom (by rw [h.src]) ≫ i⟦ f ⟧ ≫ eq_hom (by rw [h.trg])

class Model
  (φ : Type _) (α : outParam (Type _)) (ε : outParam (Type _)) [S : Signature φ α ε]
  (C : Type _) [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
               [BraidedCategoryStruct C] [Iterate C] [E : Elgot2 C ε]
  extends SigModel φ α ε C where
  copy_swap {A : Ty α} [IsRel A] : Δ_ A ≫ σ_ _ _ = copy A
  copy_assoc {A : Ty α} [IsRel A] :
    Δ_ A ≫ Δ_ A ▷ (t⟦ A ⟧ : C) ≫ (α_ _ _ _).hom = Δ_ A ≫ t⟦ A ⟧ ◁ Δ_ A
  drop_pure {A} [IsAff A] : E.eff ⊥ (drop A)
  copy_pure {A} [IsRel A] : E.eff ⊥ (copy A)
  drop_unit : drop .unit = 𝟙 (𝟙_ C)
  drop_tensor {A B} [IsAff A] [IsAff B] : drop (.tensor A B) = (drop A ⊗ drop B) ≫ (λ_ _).hom
  copy_unit : copy .unit = (λ_ _).inv
  copy_tensor {A B} [IsRel A] [IsRel B]
    : copy (.tensor A B) = (copy A ⊗ copy B) ≫ swap_inner _ _ _ _
  drop_rem {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsAff A] [IsAff B] [hf : IsRem e] : f ≫ drop _ ↠ drop _
  copy_drop_left_rem {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsAff B] [hf : IsRem e] : copy _ ≫ (f ≫ drop _) ▷ t⟦ A ⟧ ↠ (λ_ _).inv
  copy_dup_ltimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsDup e] : f ≫ copy _ ↠ copy _ ≫ (f ⋉ f)
  copy_dup_rtimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsDup e] : f ≫ copy _ ↠ copy _ ≫ (f ⋊ f)
  drop_add {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsAff A] [IsAff B] [hf : IsAdd e] : f ≫ drop _ ↞ drop _
  copy_drop_left_add {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsAff B] [hf : IsAdd e] : copy _ ≫ (f ≫ drop _) ▷ t⟦ A ⟧ ↞ (λ_ _).inv
  copy_fuse_ltimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsFuse e] : f ≫ copy _ ↞ copy _ ≫ (f ⋉ f)
  copy_fuse_rtimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsFuse e] : f ≫ copy _ ↞ copy _ ≫ (f ⋊ f)

variable [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

instance Model.dropCentral {A : Ty α} [IsAff A] : Central (C := C) (!_ A)
  := E.pure_hom_central drop_pure

instance Model.copyCentral {A : Ty α} [IsRel A] : Central (C := C) (Δ_ A)
  := E.pure_hom_central copy_pure
