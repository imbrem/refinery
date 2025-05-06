import Refinery.Term.Syntax.Basic

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v}

def subst0 (a : Term φ α) : Subst φ α | 0 => a | n + 1 => .bv n

@[simp] theorem subst0_get_zero (a : Term φ α) : a.subst0.get 0 = a := rfl

@[simp] theorem subst0_get_succ (a : Term φ α) (n : ℕ) : a.subst0.get (n + 1) = .bv n := rfl

@[simp] theorem subst0_wk0 (a b : Term φ α) : (↑⁰ a).subst b.subst0 = a
  := by rw [<-subst_renIn]; apply Term.subst_id

theorem Subst.split (σ : Subst φ α) : σ = (σ.get 0).subst0 * (σ.renIn Nat.succ).lift := by
  ext x; cases x <;> simp
