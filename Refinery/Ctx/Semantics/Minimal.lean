import Refinery.Ctx.Semantics
import Refinery.Ctx.Minimal

namespace Refinery

open CategoryTheory

open PremonoidalCategory MonoidalCategory'

open scoped MonoidalCategory

open EffectfulCategory

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [ChosenFiniteCoproducts C]
         [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε]
         [M : Model φ α ε C]

@[simp]
def Ctx?.SAt.den {v : Var? α} {Γ : Ctx? α} {n} : Γ.SAt v n → ((g⟦ Γ ⟧ : C) ⟶ v⟦ v ⟧)
  | .here (Γ := Γ) d h => ((have _ := d.del; !_ Γ.ety) ⊗ (Var?.Wk.den h)) ≫ (λ_ _).hom
  | .there x hw => (x.den ⊗ !_ _) ≫ (ρ_ _).hom

theorem Ctx?.SAt.den_unstrict {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.SAt v n)
  : x.unstrict.den (C := C) = x.den := by induction x <;> simp [*]

theorem Ctx?.SAt.den_cast {v v' : Var? α}
  {Γ Γ' : Ctx? α} {n n'} (hΓ : Γ = Γ') (hv : v = v') (hn : n = n') (x : Γ.SAt v n)
  : (x.cast hΓ hv hn).den (C := C) = eqToHom (by rw [hΓ]) ≫ x.den ≫ eqToHom (by rw [hv])
  := by cases hΓ; cases hv; cases hn; simp

theorem Ctx?.SAt.den_cast_src {v : Var? α} {Γ Γ' : Ctx? α} {n} (hΓ : Γ = Γ') (x : Γ.SAt v n)
  : (x.cast_src hΓ).den (C := C) = eqToHom (by rw [hΓ]) ≫ x.den := by cases hΓ; simp

theorem Ctx?.SAt.den_cast_trg {v v' : Var? α} {Γ : Ctx? α} {n} (hv : v = v') (x : Γ.SAt v n)
  : (x.cast_trg hv).den (C := C) = x.den ≫ eqToHom (by rw [hv]) := by cases hv; simp

theorem Ctx?.SAt.den_cast_idx {v : Var? α} {Γ : Ctx? α} {n n'} (hn : n = n') (x : Γ.SAt v n)
  : (x.cast_idx hn).den (C := C) = x.den := by cases hn; simp

theorem Ctx?.At.factor_den {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n)
  : x.toUsed.den ≫ x.strict.den = x.den (C := C) := by
  rw [<-x.strict.den_unstrict, Ctx?.At.den_pwk]
  congr; apply Subsingleton.elim

theorem Ctx?.At.factor_wk_den {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n)
  : x.toUsed.toWk.den ≫ x.strict.den = x.den (C := C) := by rw [Ctx?.PWk.den_toWk, factor_den]
