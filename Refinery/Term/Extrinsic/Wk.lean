import Refinery.Term.Extrinsic.Typing
import Refinery.Ctx.Basic

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

def Deriv.wkTerm {e : ε} {Γ Δ : Ctx? α ε} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  : (Δ ⊢[e] a : A) → Term φ (Ty α)
  | .bv (n := n) hv => .bv (ρ n)
  | .op (f := f) hf da => .op f (da.wkTerm ρ)
  | .let₁ (A := A) (B := B) hΓ da db =>
    .let₁ (da.wkTerm (hΓ.rightWk ρ)) A (db.wkTerm ((hΓ.leftWk ρ).scons _))
  | .unit _ => .unit
  | .pair hΓ da db =>
    .pair (da.wkTerm (hΓ.leftWk ρ)) (db.wkTerm (hΓ.rightWk ρ))
  | .let₂ (A := A) (B := B) hΓ da db =>
    .let₂ (da.wkTerm (hΓ.rightWk ρ)) A B (db.wkTerm (((hΓ.leftWk ρ).scons _).scons _))
  | .inl (A := A) (B := B) da => .inl A B (da.wkTerm ρ)
  | .inr (A := A) (B := B) db => .inr A B (db.wkTerm ρ)
  | .case (A := A) (B := B) hΓ da db dc =>
    .case (da.wkTerm (hΓ.rightWk ρ)) A B (db.wkTerm ((hΓ.leftWk ρ).scons _))
          (dc.wkTerm ((hΓ.leftWk ρ).scons _))
  | .abort (A := A) da => .abort A (da.wkTerm ρ)
  | .iter (A := A) (B := B) hΓ _ _ _ da db =>
    .iter (da.wkTerm (hΓ.rightWk ρ)) A B (db.wkTerm ((hΓ.leftWk ρ).scons _))

@[simp]
theorem Deriv.wkTerm_eq {e : ε} {Γ Δ : Ctx? α ε} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢[e] a : A) : D.wkTerm ρ = a.ren ρ
  := by induction D generalizing Γ <;> simp [wkTerm, *]

def Deriv.wk {e : ε} {Γ Δ : Ctx? α ε} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  : (D : Δ ⊢[e] a : A) → (Γ ⊢[e] D.wkTerm ρ : A)
  | .bv hv => .bv (hv.wkIn ρ)
  | .op hf da => .op hf (da.wk ρ)
  | .let₁ (A := A) (B := B) hΓ da db =>
    .let₁ (A := A) (B := B) (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ)) (db.wk ((hΓ.leftWk ρ).scons _))
  | .unit hv => .unit (hv.wk ρ)
  | .pair hΓ da db =>
    .pair (hΓ.wk ρ) (da.wk (hΓ.leftWk ρ)) (db.wk (hΓ.rightWk ρ))
  | .let₂ (A := A) (B := B) hΓ da db =>
    .let₂ (A := A) (B := B) (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ))
      (db.wk (((hΓ.leftWk ρ).scons _).scons _))
  | .inl (A := A) (B := B) da => .inl (da.wk ρ)
  | .inr (A := A) (B := B) db => .inr (db.wk ρ)
  | .case (A := A) (B := B) hΓ da db dc =>
    .case (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ)) (db.wk ((hΓ.leftWk ρ).scons _))
          (dc.wk ((hΓ.leftWk ρ).scons _))
  | .abort (A := A) da => .abort (da.wk ρ)
  | .iter (A := A) (B := B) hΓ hei _ _ da db =>
    .iter (hΓ.wk ρ) hei (hΓ.wkLeft_copy ρ) (hΓ.wkLeft_del ρ)
                        (da.wk (hΓ.rightWk ρ)) (db.wk ((hΓ.leftWk ρ).scons _))

end Term

end Refinery
