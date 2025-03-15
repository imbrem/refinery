import Refinery.Term.Extrinsic.Typing
import Refinery.Ctx.Semantics

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open ChosenFiniteCoproducts

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

namespace Term

def Deriv.den {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  : (Γ ⊢ a : A) → ((g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧)
  | .bv hv => hv.den
  | .op hf da => da.den ≫ hf.den
  | .let₁ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ db.den
  | .unit dΓ => !_ _
  | .pair dΓ da db => dΓ.den ≫ (da.den ⋉ db.den)
  | .let₂ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ (α_ _ _ _).inv ≫ db.den
  | .inl da => da.den ≫ CC.inl _ _
  | .inr db => db.den ≫ CC.inr _ _
  | .case dΓ da db dc => dΓ.den ≫ (_ ◁ da.den) ≫ (∂L _ _ _).inv ≫ desc db.den dc.den
  | .abort da => da.den ≫ CC.fromZero _
  | .iter (A := A) (B := B) (Γl := Γl) dΓ _ _ da db =>
    dΓ.den ≫ (_ ◁ da.den) ≫ iterate (
      Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ db.den
        ≫ (∂L g⟦Γl⟧ t⟦B⟧ t⟦A⟧).inv
        ≫ ((!_ Γl.ety ▷ _ ≫ (λ_ _).hom) ⊕ₕ 𝟙 _))

theorem Deriv.den_cast {Γ Γ' : Ctx? α} {A A' : Ty α} {a a' : Term φ (Ty α)}
  (hΓ : Γ = Γ') (hA : A = A') (ha : a = a') (D : Γ ⊢ a : A)
  : (D.cast hΓ hA ha).den (C := C) = eqToHom (by rw [hΓ]) ≫ D.den ≫ eqToHom (by rw [hA])
  := by cases hΓ; cases hA; cases ha; simp

@[simp]
theorem Deriv.den_cast_term {Γ : Ctx? α} {A : Ty α} {a a' : Term φ (Ty α)}
  (ha : a = a') (D : Γ ⊢ a : A)
  : (D.cast_term ha).den (C := C) = D.den
  := by cases ha; rfl

@[simp]
theorem Deriv.den_bv0 {Γ : Ctx? α} [hΓ : Γ.del] {A : Ty α} {q : Quant}
  : (Deriv.bv0 (Γ := Γ) (A := A) (q := q)).den (C := C) = !_ Γ.ety ▷ _ ≫ (λ_ _).hom
  := by simp [bv0, den]

@[simp]
theorem Deriv.den_bv1 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} [hv : v.del] {A : Ty α} {q : Quant}
  : (Deriv.bv1 (Γ := Γ) (A := A) (q := q) (v := v)).den (C := C)
  = !_ Γ.ety ▷ _ ▷ _ ≫ (λ_ _).hom ▷ _ ≫ t⟦A⟧ ◁ !_ v.ety ≫ (ρ_ _).hom
  := by simp [bv1, den, tensorHom_def]
