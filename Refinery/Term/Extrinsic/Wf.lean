import Refinery.Term.Extrinsic.Refinement.Relation

open HasQuant

open HasPQuant

open HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

structure Wf (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Type _ where
  tm : Term φ (Ty α)
  deriv : (Γ ⊢ tm : A)

def Deriv.wf (R : DRWS φ α) {Γ : Ctx? α} {A} {a : Term φ (Ty α)} (da : Γ ⊢ a : A) : Wf R Γ A :=
  ⟨a, da⟩

variable {R : DRWS φ α}

def Wf.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} (a : Wf R Δ A) : Wf R Γ A
  := ⟨a.tm.ren ρ, a.deriv.wk ρ⟩

theorem Wf.tm_wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} (a : Wf R Δ A)
  : (a.wk ρ).tm = a.tm.ren ρ := rfl

def Wf.subst {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} (a : Wf R Δ A) : Wf R Γ A
  := ⟨a.tm.subst σ, a.deriv.subst σ⟩

theorem Wf.tm_subst {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} (a : Wf R Δ A)
  : (a.subst σ).tm = a.tm.subst σ := rfl

instance Wf.instPreorder (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Preorder (Wf R Γ A) where
  le l r := R.refines.rel l.deriv r.deriv
  le_refl a := DRWS.uniform.refl a.deriv a.deriv
  le_trans a b c hab hbc := DRWS.uniform.trans hab hbc

instance Wf.instSetoid (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Setoid (Wf R Γ A) where
    r l r := l ≤ r ∧ r ≤ l
    iseqv := {
      refl a := ⟨le_refl a, le_refl a⟩
      symm hab := ⟨hab.right, hab.left⟩
      trans hab hbc := ⟨le_trans hab.left hbc.left, le_trans hbc.right hab.right⟩
    }

--TODO: Wf constructors

--TODO: Wf congruence

--TODO: Wf soundness
