import Refinery.Term.Extrinsic.Semantics.Typing
import Refinery.Term.Extrinsic.Minimal
import Refinery.Ctx.Semantics.Minimal

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open ChosenFiniteCoproducts

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

namespace Term

def SDeriv.den {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  : (Γ ⊢ₛ a : A) → ((g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧)
  | .bv hv => hv.den
  | .op hf da => da.den ≫ hf.den
  | .let₁ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ db.den
  | .unit dΓ => haveI _ := dΓ.del; !_ _
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

theorem SDeriv.den_cast {Γ Γ' : Ctx? α} {A A' : Ty α} {a a' : Term φ (Ty α)}
  (hΓ : Γ = Γ') (hA : A = A') (ha : a = a') (D : Γ ⊢ₛ a : A)
  : (D.cast hΓ hA ha).den (C := C) = eqToHom (by rw [hΓ]) ≫ D.den ≫ eqToHom (by rw [hA])
  := by cases hΓ; cases hA; cases ha; simp

theorem SDeriv.den_cast_term {Γ : Ctx? α} {A : Ty α} {a a' : Term φ (Ty α)}
  (ha : a = a') (D : Γ ⊢ₛ a : A)
  : (D.cast_term ha).den (C := C) = D.den
  := by cases ha; rfl

theorem SDeriv.den_unstrict {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ a : A)
  : D.unstrict.den = D.den (C := C)
  := by induction D <;> simp [den, unstrict, Deriv.den, Ctx?.SAt.den_unstrict, *]

-- theorem SDeriv.coherence {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
--   (D D' : Γ ⊢ₛ a : A) : D.den (C := C) = D'.den := by induction D with
--   | bv x => cases D' with | bv x' => rw [Subsingleton.elim x x']
--   | op => sorry
--   | _ => sorry
