import Refinery.Term.Extrinsic.Wf.Basic
import Refinery.Term.Extrinsic.Refinement.Semantics.Relation

namespace Refinery

open CategoryTheory MonoidalCategory' PremonoidalCategory DistributiveCategory
     ChosenFiniteCoproducts HasCommRel HasQuant

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

def Wf.den {R : DRWS φ α} {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : (g⟦Γ⟧ : C) ⟶ t⟦A⟧ := a.deriv.den

theorem Wf.rby.sound {R : DRWS φ α} [R.Valid C]
  {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a.rby b) : a.den (C := C) ↠ b.den
  := DRWS.Valid.den_ref a.deriv b.deriv h

theorem Wf.equiv_sound {R : DRWS φ α} [R.Valid C]
  {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a ≈ b) : a.den (C := C) = b.den
  := refines_antisymm h.left.sound h.right.sound

def Eqv.den {R : DRWS φ α} [R.Valid C] {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A) : (g⟦Γ⟧ : C) ⟶ t⟦A⟧
  := Quotient.lift Wf.den (λ _ _ h => Wf.equiv_sound h) a

theorem Eqv.rby.sound {R : DRWS φ α} [R.Valid C]
  {Γ : Ctx? α} {A : Ty α} {a b : Eqv R Γ A} (h : a.rby b) : a.den (C := C) ↠ b.den
  := by induction a, b using Eqv.quotInd₂; exact h.exact.sound
