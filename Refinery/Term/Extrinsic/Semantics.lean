import Refinery.Term.Extrinsic.Typing
import Refinery.Ctx.Semantics

namespace Refinery

open CategoryTheory

open Monoidal

open MonoidalCategory

open ChosenFiniteCoproducts

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategoryStruct C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

namespace Term

def Wf.den {Γ : Ctx? α ε} {A : Ty α} {a : Term φ} : (Γ ⊢ a : A) → ((g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧)
  | .bv hv => hv.den
  | .op hf da => da.den ≫ hf.den
  | .let₁ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ db.den
  | .unit dΓ => dΓ.den
  | .pair dΓ da db => dΓ.den ≫ (da.den ⋉ db.den)
  | .let₂ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ (α_ _ _ _).inv ≫ db.den
  | .inl da => da.den ≫ CC.inl _ _
  | .inr db => db.den ≫ CC.inr _ _
  | .case dΓ da db dc => dΓ.den ≫ (_ ◁ da.den) ≫ (∂L _ _ _).inv ≫ desc db.den dc.den
  | .abort da => da.den ≫ CC.fromZero _
  | .iter (A := A) (B := B) (Γr := Γr) dΓ _ _ da db =>
    dΓ.den ≫ (_ ◁ da.den) ≫ iterate (
      Δ_ Γr.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ db.den
        ≫ (∂L g⟦Γr⟧ t⟦B⟧ t⟦A⟧).inv
        ≫ ((!_ Γr.ety ▷ _ ≫ (λ_ _).hom) ⊕ₕ 𝟙 _))

def Deriv.den {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ}
  : (Γ ⊢[e] a : A) → ((g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧)
  | .bv hv => hv.den
  | .op hf da => da.den ≫ hf.den
  | .let₁ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ db.den
  | .unit dΓ => dΓ.den
  | .pair dΓ da db => dΓ.den ≫ (da.den ⋉ db.den)
  | .let₂ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ (α_ _ _ _).inv ≫ db.den
  | .inl da => da.den ≫ CC.inl _ _
  | .inr db => db.den ≫ CC.inr _ _
  | .case dΓ da db dc => dΓ.den ≫ (_ ◁ da.den) ≫ (∂L _ _ _).inv ≫ desc db.den dc.den
  | .abort da => da.den ≫ CC.fromZero _
  | .iter (A := A) (B := B) (Γr := Γr) dΓ _ _ _ da db =>
    dΓ.den ≫ (_ ◁ da.den) ≫ iterate (
      Δ_ Γr.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ db.den
        ≫ (∂L g⟦Γr⟧ t⟦B⟧ t⟦A⟧).inv
        ≫ ((!_ Γr.ety ▷ _ ≫ (λ_ _).hom) ⊕ₕ 𝟙 _))

theorem Deriv.den_toWf {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ}
  (D : Γ ⊢[e] a : A) : D.toWf.den = D.den (C := C)
  := by induction D <;> simp only [toWf, den, Wf.den, *]
