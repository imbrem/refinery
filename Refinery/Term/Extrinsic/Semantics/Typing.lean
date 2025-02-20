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

def Deriv.den {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
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
  | .iter (A := A) (B := B) (Γl := Γl) dΓ _ _ _ da db =>
    dΓ.den ≫ (_ ◁ da.den) ≫ iterate (
      Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ db.den
        ≫ (∂L g⟦Γl⟧ t⟦B⟧ t⟦A⟧).inv
        ≫ ((!_ Γl.ety ▷ _ ≫ (λ_ _).hom) ⊕ₕ 𝟙 _))

@[simp]
theorem Deriv.den_mono {e e' : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
  (he : e ≤ e') (D : Γ ⊢[e] a : A) : (D.mono he).den = D.den (C := C)
  := by induction D with
  | bv => simp only [den, mono]; rw [Ctx?.At.den_eff]
  | _ => simp only [den, mono, *] <;> rfl
