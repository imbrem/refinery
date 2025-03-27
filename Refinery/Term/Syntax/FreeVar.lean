import Refinery.Term.Syntax.Basic

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v}

def fvi : Term φ α → ℕ
  | .bv ix => ix + 1
  | .op _ a => fvi a
  | .let₁ a _ b => max (fvi a) (fvi b - 1)
  | .let₂ a _ _ b => max (fvi a) (fvi b - 2)
  | .unit => 0
  | .pair a b => max (fvi a) (fvi b)
  | .inl _ _ a => fvi a
  | .inr _ _ b => fvi b
  | .case a _ _ b c => max (fvi a) (max (fvi b - 1) (fvi c - 1))
  | .abort _ a => fvi a
  | .iter a _ _ b => max (fvi a) (fvi b - 1)
  | .invalid => 0

theorem Subst.eqOn_pred_eqOn_lift (σ σ' : Subst φ α) (k : ℕ)
  : (∀n < k - 1, σ.get n = σ'.get n) → (∀n < k, σ.lift.get n = σ'.lift.get n)
  := λh n hn => match n with | 0 => rfl | n + 1 => by simp only [Subst.get_lift_succ]; rw [h]; omega

theorem Subst.subst_eqOn_fvi {a : Term φ α} (σ σ' : Subst φ α) (h : ∀n < a.fvi, σ.get n = σ'.get n)
  : a.subst σ = a.subst σ' := by
  induction a generalizing σ σ' with
  | bv => apply h; simp [fvi]
  | _ =>
    simp only [fvi, lt_sup_iff, or_imp, forall_and] at h
    (try casesm* _ ∧ _)
    simp
    repeat first | apply And.intro | apply_assumption | apply eqOn_pred_eqOn_lift

theorem Subst.smul_eqOn_fvi {a : Term φ α} (σ σ' : Subst φ α) (h : ∀n < a.fvi, σ.get n = σ'.get n)
  : σ • a = σ' • a := subst_eqOn_fvi σ σ' h

theorem Subst.subst1_fvi {a : Term φ α} (σ : Subst φ α) (h : ∀n < a.fvi, σ.get n = .bv n)
  : a.subst σ = a := by convert σ.subst_eqOn_fvi 1 h; simp

theorem Subst.smul1_fvi {a : Term φ α} (σ : Subst φ α) (h : ∀n < a.fvi, σ.get n = .bv n)
  : σ • a = a := subst1_fvi σ h

end Term

end Refinery
