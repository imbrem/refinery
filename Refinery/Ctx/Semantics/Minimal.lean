import Refinery.Ctx.Semantics
import Refinery.Ctx.Minimal
import Refinery.Ctx.Semantics.Coherence

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

def Var?.ZWk.den {u v : Var? α} : u.ZWk v → ((v⟦ u ⟧ : C) ⟶ v⟦ v ⟧)
  | .refl _ => 𝟙 _
  | .erase h => haveI _ := h.ety_aff; !_ _

@[simp]
theorem Var?.ZWk.den_refl {v : Var? α} : (ZWk.refl v).den (C := C) = 𝟙 _ := rfl

@[simp]
theorem Var?.ZWk.den_erase {A : Ty α} {q : EQuant} (h : Var?.del ⟨A, q⟩)
  : (Var?.ZWk.erase h).den (C := C) = haveI _ := h.ety_aff; !_ _ := rfl

theorem Var?.ZWk.den_toWk {u v : Var? α} (ρ : u.ZWk v) : ρ.toWk.den (C := C) = ρ.den := by
  cases ρ <;> simp

theorem Var?.ZWk.coherence {u v : Var? α} (ρ ρ' : u.ZWk v) : ρ.den (C := C) = ρ'.den
  := by rw [<-ρ.den_toWk, <-ρ'.den_toWk]

instance Var?.ZWk.den_pure {u v : Var? α} (ρ : u.ZWk v) : E.HasEff e ρ.den := by
  rw [<-ρ.den_toWk]; infer_instance

instance Var?.ZWk.den_central {u v : Var? α} (ρ : u.ZWk v) : Central (C := C) ρ.den := by
  rw [<-ρ.den_toWk]; infer_instance

@[simp]
def Ctx?.ZWk.den {Γ : Ctx? α} {Δ : Ctx? α} : Γ.ZWk Δ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧)
  | .nil => 𝟙 (𝟙_ C)
  | .cons ρ h => ρ.den ⊗ h.den

theorem Ctx?.ZWk.den_nil : (Ctx?.ZWk.nil).den (M := M) = 𝟙 (𝟙_ C) := rfl

theorem Ctx?.ZWk.den_cons {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) {v w : Var? α} (h : v.ZWk w)
  : (Ctx?.ZWk.cons ρ h).den = ρ.den (C := C) ⊗ h.den := rfl

theorem Ctx?.ZWk.den_toPWk {Γ : Ctx? α} {Δ : Ctx? α} (ρ : Γ.ZWk Δ) : ρ.toPWk.den (C := C) = ρ.den
  := by induction ρ with | nil => rfl | cons ρ h => cases h <;> simp [*]

@[simp]
theorem Ctx?.ZWk.den_refl {Γ : Ctx? α} : (ZWk.refl Γ).den (C := C) = 𝟙 _ := by
  rw [<-den_toPWk]; simp

theorem Ctx?.ZWk.coherence {Γ : Ctx? α} {Δ : Ctx? α} (ρ ρ' : Γ.ZWk Δ)
  : ρ.den (C := C) = ρ'.den
  := by rw [<-ρ.den_toPWk, <-ρ'.den_toPWk, Subsingleton.elim ρ.toPWk ρ'.toPWk]

theorem Ctx?.ZWk.den_comp {Γ Δ Ξ : Ctx? α} (ρ : Γ.ZWk Δ) (σ : Δ.ZWk Ξ)
  : (ρ.comp σ).den (C := C) = ρ.den ≫ σ.den := by
  rw [<-ρ.den_toPWk, <-σ.den_toPWk, PWk.den_comp, <-den_toPWk]
  congr; apply Subsingleton.elim

instance Ctx?.ZWk.den_pure {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) : E.HasEff e ρ.den := by
  rw [<-ρ.den_toPWk]; infer_instance

instance Ctx?.ZWk.den_central {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) : Central (C := C) ρ.den := by
  rw [<-ρ.den_toPWk]; infer_instance

@[reassoc]
theorem Ctx?.At.den_zwk {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) {v n} (x : Δ.At v n)
  : ρ.den ≫ x.den = (x.pwk ρ.toPWk).den (C := C) := by rw [<-den_pwk, ZWk.den_toPWk]

@[reassoc]
theorem Ctx?.At.factor_den {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n)
  : x.toUsed.den ≫ x.strict.den = x.den (C := C) := by
  rw [<-x.strict.den_unstrict, Ctx?.At.den_zwk]
  congr; apply Subsingleton.elim

@[reassoc]
theorem Ctx?.At.factor_pwk_den {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n)
  : x.toUsed.toPWk.den ≫ x.strict.den = x.den (C := C)
  := by rw [Ctx?.ZWk.den_toPWk, factor_den]

@[reassoc]
theorem Ctx?.At.factor_wk_den {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n)
  : x.toUsed.toPWk.toWk.den ≫ x.strict.den = x.den (C := C)
  := by rw [Ctx?.PWk.den_toWk, factor_pwk_den]

theorem Ctx?.SAt.den_strict_unstrict {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.SAt v n)
  : x.unstrict.strict.den (C := C) = eqToHom (by rw [x.unstrict_used_eq]) ≫ x.den
  := by rw [x.strict_unstrict, den_cast_src]

@[reassoc]
theorem Ctx?.SSplit.den_fuse {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (ρ : Δ.ZWk Δ') (ρ' : Ξ.ZWk Ξ')
  : σ.den (C := C) ≫ (ρ.den ⊗ ρ'.den) = (σ.fuseWk ρ ρ').den ≫ (σ.fuse ρ ρ').den
  := by
  rw [
    <-ρ.den_toPWk, <-ρ'.den_toPWk, <-σ.den_unstrict, σ.unstrict.den_wkOut, <-Ctx?.ZWk.den_toPWk,
    <-Ctx?.SSplit.den_unstrict, Ctx?.Split.den_wkIn
  ]
  apply Ctx?.Split.coherence
