import Refinery.Term.Extrinsic.Typing
import Refinery.Ctx.Add

namespace Refinery

namespace Term

open HasQuant

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive Deriv? : Ctx? α ε → Var? α ε → Term φ (Ty α) → Type _
  | valid {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢[e] a : A) (q : EQuant)
    (hΓ : q ≤ quant Γ) : Deriv? Γ ⟨A, q, e⟩ a
  | zero {Γ : Ctx? α ε} (hΓ : Γ.del) (a A e) : Deriv? Γ ⟨A, 0, e⟩ a

notation Γ "⊢?" a ":" v => Deriv? Γ v a

abbrev Deriv?.erase {Γ : Ctx? α ε} {v : Var? α ε} {a : Term φ (Ty α)} (_D : Γ ⊢? a : v)
  : (Γ.erase ⊢? a : v.erase) := .zero inferInstance _ _ _

def Deriv?.splitLeft {Γ : Ctx? α ε} {u v w : Var? α ε} {a : Term φ (Ty α)}
  : (h : u.PSSplit v w) → (Γ ⊢? a : u) → (h.leftCtx Γ ⊢? a : v)
  | .left _, D => D | .sboth _, D => D
  | .right _, D => D.erase

def Deriv?.splitRight {Γ : Ctx? α ε} {u v w : Var? α ε} {a : Term φ (Ty α)}
  : (h : u.PSSplit v w) → (Γ ⊢? a : u) → (h.rightCtx Γ ⊢? a : w)
  | .left _, D => D.erase | .sboth _, D => D
  | .right _, D => D

def Deriv?.unused {Γ : Ctx? α ε} {v : Var? α ε} (hΓ : Γ.del)  (a : Term φ (Ty α)) (hv : v.unused)
  : (Γ ⊢? a : v) := match v with | ⟨A, 0, e⟩ => .zero hΓ a A e

theorem Deriv?.copy {Γ : Ctx? α ε} {v : Var? α ε} {a : Term φ (Ty α)}
  (D : Γ ⊢? a : v) (hv : v.used) (hc : v.copy) : Γ.copy := by cases D with
  | valid D q hΓ =>
    cases q using EQuant.casesZero with
    | zero => cases hv
    | rest q =>
      constructor
      rw [<-EQuant.coe_le_coe]
      apply le_trans _ hΓ
      simp [Var?.copy_iff] at hc
      exact hc.q
  | zero => cases hv

inductive SubstDS (φ) {α ε} [S : Signature φ α ε] : Ctx? α ε → Ctx? α ε → Type _
  | nil {Γ} (hΓ : Γ.del) : SubstDS φ Γ .nil
  | cons {Γ Γl Γr Δ} {v} {a : Term φ _} (hΓ : Γ.PSSplit Γl Γr)
    (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v) : SubstDS φ Γ (Δ.cons v)

def SubstDS.toSubst {Γ Δ} : SubstDS φ Γ Δ → Subst φ (Ty α)
  | .nil _, i => .invalid
  | .cons (a := a) .., 0 => a
  | .cons _ σ _, i + 1 => σ.toSubst i

instance SubstDS.coeSubst : CoeOut (SubstDS φ Γ Δ) (Subst φ (Ty α)) where
  coe := SubstDS.toSubst

def SubstDS.tailCtx {Γ Δ} : SubstDS φ Γ Δ → Ctx? α ε
  | .nil _ => Γ
  | .cons (Γl := Γl) .. => Γl

def SubstDS.headCtx {Γ Δ} : SubstDS φ Γ Δ → Ctx? α ε
  | .nil _ => Γ.erase
  | .cons (Γr := Γr) .. => Γr

def SubstDS.headSplit {Γ Δ} : (σ : SubstDS φ Γ Δ) → Γ.PSSplit (σ.tailCtx) (σ.headCtx)
  | .nil _ => Γ.erase_right
  | .cons hΓ .. => hΓ

def SubstDS.head {Γ Δ} : SubstDS φ Γ Δ → Var? α ε
  | .nil _ => ⟨.unit, 0, ⊥⟩
  | .cons (v := v) .. => v

def SubstDS.headD {Γ Δ} : (σ : SubstDS φ Γ Δ) → σ.headCtx ⊢? (σ.toSubst 0) : σ.head
  | .nil hΓ => .zero (by simp [headCtx]) _ _ _
  | .cons _ _ da => da

def SubstDS.tail {Γ Δ} : (σ : SubstDS φ Γ Δ) → SubstDS φ σ.tailCtx Δ.tail
  | .nil hΓ => .nil hΓ
  | .cons _ σ _ => σ

structure SubstSplit (φ) {α ε} [S : Signature φ α ε] (inCtx outCtx outLeft outRight : Ctx? α ε)
  where
  (inLeft inRight : Ctx? α ε)
  (splitIn : inCtx.PSSplit inLeft inRight)
  (substLeft : SubstDS φ inLeft outLeft)
  (substRight : SubstDS φ inRight outRight)

def SubstSplit.erase_right (Γ : Ctx? α ε) [hΓ : Γ.del] : SubstSplit φ Γ .nil .nil .nil
  := ⟨Γ, Γ.erase, Γ.erase_right, .nil hΓ, .nil inferInstance⟩

def SubstSplit.erase_left (Γ : Ctx? α ε) [hΓ : Γ.del] : SubstSplit φ Γ .nil .nil .nil
  := ⟨Γ.erase, Γ, Γ.erase_left, .nil inferInstance, .nil hΓ⟩

def SubstDS.split {Γ Δl Δr : Ctx? α ε}
  : SubstDS φ Γ Δ → Δ.PSSplit Δl Δr → SubstSplit φ Γ Δ Δl Δr
  | .nil hΓ, .nil => SubstSplit.erase_right _
  | .cons (Γr := Γr) (v := v) (a := a) hΓ σ da, .cons hΔ hlr =>
    let s := σ.split hΔ
    match hlr with
    | .left _ =>
      let Ξ := hΓ.c12_3_23 s.splitIn.comm
      let s1_23 : Γ.PSSplit s.inRight Ξ := hΓ.s12_3_1_23 s.splitIn.comm
      let s23 : Ξ.PSSplit s.inLeft Γr := hΓ.s12_3_23 s.splitIn.comm
      ⟨Ξ, s.inRight,
        s1_23.comm,
        s.substLeft.cons s23 da,
        s.substRight.cons s.inRight.erase_right (.zero inferInstance a _ _)⟩
    | .right _ =>
      let Ξ := hΓ.c12_3_23 s.splitIn
      let s1_23 : Γ.PSSplit s.inLeft Ξ := hΓ.s12_3_1_23 s.splitIn
      let s23 : Ξ.PSSplit s.inRight Γr := hΓ.s12_3_23 s.splitIn
      ⟨s.inLeft, Ξ,
        s1_23,
        s.substLeft.cons s.inLeft.erase_right (.zero inferInstance a _ _),
        s.substRight.cons s23 da⟩
    | .sboth h =>
      if hv : v.used then
        have sr := Γr.both (hΓ := da.copy hv h.copy);
        ⟨hΓ.c12_34_13 s.splitIn sr, hΓ.c12_34_24 s.splitIn sr,
          hΓ.s12_34_13_24 s.splitIn sr,
          s.substLeft.cons (hΓ.s12_34_13 s.splitIn sr) da,
          s.substRight.cons (hΓ.s12_34_24 s.splitIn sr) da⟩
      else
        have hv := ((Var?.unused_iff _).mpr hv);
        let Ξ := hΓ.c12_3_23 s.splitIn
        let s1_23 : Γ.PSSplit s.inLeft Ξ := hΓ.s12_3_1_23 s.splitIn
        let s23 : Ξ.PSSplit s.inRight Γr := hΓ.s12_3_23 s.splitIn
        ⟨s.inLeft, Ξ,
          s1_23,
          s.substLeft.cons s.inLeft.erase_right (.unused inferInstance a hv),
          s.substRight.cons s23 da⟩

-- def SubstDS.splitLeft {Γ Δ Δl Δr} : SubstDS φ Γ Δ → Δ.PSSplit Δl Δr → Ctx? α ε
--   | _ => sorry

-- def SubstDS.wkIn {Γ' Γ Δ} (ρ : Γ'.Wk Γ) : SubstDS φ Γ Δ → SubstDS φ Γ' Δ
--   | .nil hΓ => .nil (hΓ.wk ρ)
--   | .cons (a := a) hΓ σ da => .cons (a := a) (hΓ.wk' ρ) (σ.wkIn (hΓ.leftWk' ρ)) sorry
