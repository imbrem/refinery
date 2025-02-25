import Refinery.Ctx.Basic
import Refinery.Ctx.SSplit

namespace Refinery

open HasQuant

inductive Ctx?.IsZero : Ctx? α → Prop where
  | nil : IsZero .nil
  | cons {Γ A} (hΓ : IsZero Γ) : IsZero (Ctx?.cons Γ ⟨A, 0⟩)

attribute [simp] Ctx?.IsZero.nil Ctx?.IsZero.cons

@[simp]
theorem Ctx?.erase_is_zero {Γ : Ctx? α} : Γ.erase.IsZero := by induction Γ <;> simp [*]

variable [HasQuant α]

@[simp]
theorem Ctx?.IsZero.del {Γ : Ctx? α} (h : Γ.IsZero) : Γ.del := by induction h <;> simp [*]

inductive Ctx?.SAt : Var? α → Ctx? α → ℕ → Type _ where
  | here {Γ} (d : Γ.IsZero) {w} : w ≤ v → Ctx?.SAt v (Ctx?.cons Γ w) 0
  | there {Γ n} (x : Ctx?.SAt v Γ n) (A) : Ctx?.SAt v (Ctx?.cons Γ ⟨A, 0⟩) (n + 1)

@[simp]
def Ctx?.SAt.unstrict {v : Var? α} {Γ : Ctx? α} {n} : Γ.SAt v n → Γ.At v n
  | .here d hw => .here (by simp [*]) hw
  | .there x A => .there x.unstrict (by simp)

@[simp]
def Ctx?.At.used {v : Var? α} {Γ : Ctx? α} {n} : Γ.At v n → Ctx? α
  | .here (Γ := Γ) (w := w) _ _ => Γ.erase.cons w
  | .there (w := w) x _ => x.used.cons w.erase

@[simp]
def Ctx?.At.unused {v : Var? α} {Γ : Ctx? α} {n} : Γ.At v n → Ctx? α
  | .here (Γ := Γ) (w := w) _ _ => Γ.cons w.erase
  | .there (w := w) x _ => x.unused.cons w

@[simp]
instance Ctx?.At.unused_del {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n) : x.unused.del
  := by induction x <;> simp [*]

@[simp]
instance Ctx?.At.used_del {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n) [hv : v.del] : x.used.del
  := by induction x with | here _ hw => simp [hv.anti hw] | there => simp [*]

@[simp]
def Ctx?.At.toUsed {v : Var? α} {Γ : Ctx? α} {n} : (x : Γ.At v n) → Γ.PWk x.used
  | .here (Γ := Γ) _ hvw => Γ.erasePWk.cons (le_refl _)
  | .there (w := w) x hw => x.toUsed.cons (w.del_iff_erase_le.mp hw)

@[simp]
def Ctx?.At.strict {v : Var? α} {Γ : Ctx? α} {n} : (x : Γ.At v n) → x.used.SAt v n
  | .here _ hvw => .here (by simp) hvw
  | .there x hw => .there x.strict _

@[simp]
def Ctx?.At.ssplit {v : Var? α} {Γ : Ctx? α} {n} : (x : Γ.At v n) → SSplit Γ x.used x.unused
  | .here (Γ := Γ) (w := w) _ _ => Γ.erase_left.cons (.left w)
  | .there (w := w) x _ => x.ssplit.cons (.right w)
