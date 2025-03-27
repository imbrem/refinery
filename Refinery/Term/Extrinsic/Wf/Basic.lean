import Refinery.Term.Extrinsic.Refinement.Relation

open HasQuant HasPQuant HasCommRel

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

def Wf.rby {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : Prop := R.refines.rel a.deriv b.deriv

theorem Wf.rby_refl {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : a.rby a
  := DRWS.uniform.refl a.deriv a.deriv

theorem Wf.rby.trans {Γ : Ctx? α} {A : Ty α} {a b c : Wf R Γ A}
  (hab : a.rby b) (hbc : b.rby c) : a.rby c
  := DRWS.uniform.trans hab hbc

instance Wf.instPreorder (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Preorder (Wf R Γ A) where
  le := rby
  le_refl a := a.rby_refl
  le_trans _ _ _ := rby.trans

instance Wf.setoid (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Setoid (Wf R Γ A) where
    r l r := l ≤ r ∧ r ≤ l
    iseqv := {
      refl a := ⟨le_refl a, le_refl a⟩
      symm hab := ⟨hab.right, hab.left⟩
      trans hab hbc := ⟨le_trans hab.left hbc.left, le_trans hbc.right hab.right⟩
    }

def Eqv (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) := Quotient (Wf.setoid R Γ A)

def Eqv.rby {Γ : Ctx? α} {A : Ty α} (a b : Eqv R Γ A) : Prop
  := Quotient.liftOn₂ a b Wf.rby (λ_ _ _ _ ha hb
    => propext ⟨λ r => ha.right.trans (r.trans hb.left), λ r => ha.left.trans (r.trans hb.right)⟩)

theorem Wf.rby_quot_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : Eqv.rby ⟦a⟧ ⟦b⟧ ↔ a.rby b
  := Iff.rfl

def Eqv.mk {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : Eqv R Γ A := ⟦a⟧

notation "e⟦" a "⟧" => Eqv.mk a

theorem Wf.rby_mk_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : e⟦a⟧.rby e⟦b⟧ ↔ a.rby b
  := Wf.rby_quot_iff a b

theorem Eqv.quotInd {Γ : Ctx? α} {A : Ty α} {motive : Eqv R Γ A → Prop} (a : Eqv R Γ A)
  (h : ∀ a : Wf R Γ A, motive e⟦a⟧) : motive a := Quotient.inductionOn a h

theorem Eqv.quotInd₂ {Γ : Ctx? α} {A : Ty α} {motive : Eqv R Γ A → Eqv R Γ A → Prop}
  (a b : Eqv R Γ A) (h : ∀ a b : Wf R Γ A, motive e⟦a⟧ e⟦b⟧) : motive a b
  := Quotient.inductionOn₂ a b h

theorem Eqv.quotInd₃ {Γ : Ctx? α} {A : Ty α} {motive : Eqv R Γ A → Eqv R Γ A → Eqv R Γ A → Prop}
  (a b c : Eqv R Γ A) (h : ∀ a b c : Wf R Γ A, motive e⟦a⟧ e⟦b⟧ e⟦c⟧) : motive a b c
  := Quotient.inductionOn₃ a b c h

theorem Eqv.sound {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a ≈ b) : e⟦a⟧ = e⟦b⟧
  := Quotient.sound h

theorem Eqv.exact {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : e⟦a⟧ = e⟦b⟧) : a ≈ b
  := Quotient.exact h

theorem Wf.rby.eqv {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a.rby b) : e⟦a⟧.rby e⟦b⟧
  := h

theorem Eqv.rby.exact {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : e⟦a⟧.rby e⟦b⟧) : a.rby b
  := h

theorem Eqv.mk_eq_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : e⟦a⟧ = e⟦b⟧ ↔ a ≈ b
  := ⟨exact, sound⟩

theorem Eqv.rby_refl {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A) : a.rby a
  := by induction a using Quotient.inductionOn; simp [rby, Wf.rby_refl]

theorem Eqv.rby.trans {Γ : Ctx? α} {A : Ty α} {a b c : Eqv R Γ A} (hab : a.rby b) (hbc : b.rby c)
  : a.rby c := by induction a, b, c using quotInd₃; apply Wf.rby.trans <;> assumption

theorem Eqv.rby.antisymm {Γ : Ctx? α} {A : Ty α} {a b : Eqv R Γ A} (hab : a.rby b) (hba : b.rby a)
  : a = b := by induction a, b using Eqv.quotInd₂; exact sound ⟨hab, hba⟩

instance Eqv.instPartialOrder (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α)
  : PartialOrder (Eqv R Γ A) where
  le := rby
  le_refl a := a.rby_refl
  le_trans _ _ _ := rby.trans
  le_antisymm _ _ := rby.antisymm

--TODO: Wf constructors

--TODO: Eqv constructors (lifted)
