import Refinery.Term.Extrinsic.Typing

namespace Refinery

namespace Term

open HasQuant

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive Deriv? : Ctx? α ε → Var? α ε → Term φ (Ty α) → Type _
  | valid {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢[e] a : A) (q : EQuant)
    (hΓ : q ≤ quant Γ) : Deriv? Γ ⟨A, q, e⟩ a
  | zero {Γ : Ctx? α ε} (hΓ : Γ.del) (a A e) : Deriv? Γ ⟨A, 0, e⟩ a

notation Γ "⊢?" a ":" v => Deriv? Γ v a

-- def Deriv?.erase {Γ : Ctx? α ε} {v : Var? α ε} {a : Term φ (Ty α)}
--   : (Γ ⊢? a : v) → (Γ.erase ⊢? a : v.erase)
--   | .valid D q hΓ => .zero inferInstance _ _ _
--   | .zero hΓ a A e => .zero inferInstance _ _ _

-- def Deriv?.splitLeft {Γ : Ctx? α ε} {u v w : Var? α ε} {a : Term φ (Ty α)}
--   : (h : u.PSSplit v w) → (Γ ⊢? a : u) → (h.leftCtx Γ ⊢? a : v)
--   | .left _, D => D | .sboth _, D => D
--   | .right _, _ => sorry

inductive SubstDS (φ) {α ε} [S : Signature φ α ε] : Ctx? α ε → Ctx? α ε → Type _
  | nil {Γ} (hΓ : Γ.del) : SubstDS φ Γ nil
  | cons {Γ Γl Γr Δ} {v} {a : Term φ _} (hΓ : Γ.PSSplit Γl Γr)
    (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v) : SubstDS φ Γ (Δ.cons v)

def SubstDS.toSubst {Γ Δ} : SubstDS φ Γ Δ → Subst φ (Ty α)
  | .nil _, i => .invalid
  | .cons (a := a) .., 0 => a
  | .cons _ σ _, i + 1 => σ.toSubst i

instance SubstDS.coeSubst : CoeOut (SubstDS φ Γ Δ) (Subst φ (Ty α)) where
  coe := SubstDS.toSubst

def SubstDS.leftCtx {Γ Δ} : SubstDS φ Γ Δ → Ctx? α ε
  | .nil _ => Γ
  | .cons (Γl := Γl) .. => Γl

def SubstDS.rightCtx {Γ Δ} : SubstDS φ Γ Δ → Ctx? α ε
  | .nil _ => Γ.erase
  | .cons (Γr := Γr) .. => Γr

def SubstDS.splitCtx {Γ Δ} : (σ : SubstDS φ Γ Δ) → Γ.PSSplit (σ.leftCtx) (σ.rightCtx)
  | .nil _ => Γ.erase_right
  | .cons hΓ .. => hΓ

def SubstDS.head {Γ Δ} : SubstDS φ Γ Δ → Var? α ε
  | .nil _ => ⟨.unit, 0, ⊥⟩
  | .cons (v := v) .. => v

def SubstDS.headD {Γ Δ} : (σ : SubstDS φ Γ Δ) → σ.rightCtx ⊢? (σ.toSubst 0) : σ.head
  | .nil hΓ => .zero (by simp [rightCtx]) _ _ _
  | .cons _ _ da => da

def SubstDS.tail {Γ Δ} : (σ : SubstDS φ Γ Δ) → SubstDS φ σ.leftCtx Δ.tail
  | .nil hΓ => .nil hΓ
  | .cons _ σ _ => σ

-- def SubstDS.wkIn {Γ' Γ Δ} (ρ : Γ'.Wk Γ) : SubstDS φ Γ Δ → SubstDS φ Γ' Δ
--   | .nil hΓ => .nil (hΓ.wk ρ)
--   | .cons (a := a) hΓ σ da => .cons (a := a) (hΓ.wk' ρ) (σ.wkIn (hΓ.leftWk' ρ)) sorry
