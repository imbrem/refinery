import Refinery.Term.Syntax.Basic
import Refinery.Ctx.Basic

namespace Refinery

open Term

variable {φ : Type u} {α : Type v}

--TODO: de-generalize to β = Ty α?

def Var?.packTerm (v : Var? α) : Term φ β := if v.used then .bv 0 else .unit

def Ctx?.packTerm : Ctx? α → Term φ β
  | .nil => .unit
  | .cons Γ v => .pair (↑⁰ Γ.packTerm) (v.packTerm)

namespace Term

def letCtx (G : Term φ (Ty α)) (Γ : Ctx? α) (t : Term φ (Ty α)) : Term φ (Ty α)
  := match Γ with
  | .nil => .let₁ G .unit t
  | .cons Γ v => .let₂ G Γ.ety v.ety (letCtx (.bv 1) Γ (↑¹ t))

def unpacked (Γ : Ctx? α) (t : Term φ (Ty α)) : Term φ (Ty α) := letCtx (.bv 0) Γ (↑⁰ t)
