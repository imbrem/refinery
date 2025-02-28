import Refinery.Term.Extrinsic.Minimal
import Refinery.Ctx.Semantics.Minimal
import Refinery.Term.Extrinsic.Semantics.Wk

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
  | .let₁ dΓ dq da db => dΓ.den ≫ (_ ◁ da.den) ≫ (_ ◁ dq.den) ≫ db.den
  | .unit dΓ => haveI _ := dΓ.del; !_ _
  | .pair dΓ da db => dΓ.den ≫ (da.den ⋉ db.den)
  | .let₂ dΓ dqa dqb da db => dΓ.den ≫ (_ ◁ da.den)
    ≫ (α_ _ _ _).inv
    ≫ (_ ◁ dqa.den) ▷ _
    ≫ _ ◁ dqb.den ≫ db.den
  | .inl da => da.den ≫ CC.inl _ _
  | .inr db => db.den ≫ CC.inr _ _
  | .case dΓ dΓl dqa dqb da db dc =>
    dΓ.den ≫ (_ ◁ da.den) ≫ (∂L _ _ _).inv
           ≫ desc ((dΓl.zwkLeft.den ⊗ dqa.den) ≫ db.den) ((dΓl.zwkRight.den ⊗ dqb.den) ≫ dc.den)
  | .abort da => da.den ≫ CC.fromZero _
  | .iter (A := A) (B := B) (Γl := Γl) dΓ dq _ _ da db =>
    dΓ.den ≫ (_ ◁ da.den) ≫ iterate (
      Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ _ ◁ dq.den
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
  : D.unstrict.den = D.den (C := C) := by
  induction D <;> simp [
    den, unstrict, Deriv.den, Deriv.den_pwk, tensorHom_def, Ctx?.SAt.den_unstrict,
    Ctx?.ZWk.den_toPWk, *]

def FDeriv.den {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ' a : A)
  : (g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧ := D.drop.den ≫ D.deriv.den

theorem FDeriv.den_toDeriv {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ' a : A)
  : D.toDeriv.den (C := C) = D.den := by simp only [toDeriv, Deriv.den_pwk, Ctx?.ZWk.den_toPWk,
    SDeriv.den_unstrict, den]

theorem SDeriv.coherence {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (D D' : Γ ⊢ₛ a : A) : D.den (C := C) = D'.den := by induction D with
  | bv x => cases D' with | bv x' => rw [Subsingleton.elim x x']
  | op hf => cases D' with | op hf' =>
    cases hf.trg; cases hf'.trg; cases hf.src; cases hf'.src
    simp only [den]; congr 1; apply_assumption
  | let₁ =>
    cases D'
    simp only [den]
    rename Ctx?.SSplit _ _ _ => hΓ
    sorry
  | _ => sorry

theorem FDeriv.coherence {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (D D' : Γ ⊢ₛ' a : A) : D.den (C := C) = D'.den := sorry

theorem Deriv.den_factor {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ a : A)
  : D.factor.den (C := C) = D.den := sorry

theorem Deriv.coherence {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (D D' : Γ ⊢ a : A) : D.den (C := C) = D'.den
  := by rw [<-D.den_factor, <-D'.den_factor, D.factor.coherence D'.factor]
