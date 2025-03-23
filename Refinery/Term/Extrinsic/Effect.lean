import Refinery.Signature
import Refinery.Term.Syntax.Basic

namespace Refinery

open HasQuant

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive HasEff : ε → Term φ (Ty α) → Prop
  | bv (n) : HasEff e .(bv n)
  | op {e f a} : S.FnEff e f → HasEff e a → HasEff e (.op f a)
  | let₁ {e A a b} : HasEff e a → HasEff e b → HasEff e (.let₁ a A b)
  | let₂ {e A B a b} : HasEff e a → HasEff e b → HasEff e (.let₂ a A B b)
  | unit : HasEff e .unit
  | pair {e a b} : HasEff e a → HasEff e b → HasEff e (.pair a b)
  | inl {e A B a} : HasEff e a → HasEff e (.inl A B a)
  | inr {e A B b} : HasEff e b → HasEff e (.inr A B b)
  | case {e A B a b c} : HasEff e a → HasEff e b → HasEff e c → HasEff e (.case a A B b c)
  | abort {e A a} : HasEff e a → HasEff e (.abort A a)
  | iter {e A B a b} : e ∈ S.iterative → HasEff e a → HasEff e b → HasEff e (.iter a A B b)
  | invalid {e} : HasEff e .invalid

attribute [class] HasEff

attribute [simp, instance] HasEff.bv HasEff.unit HasEff.invalid

instance HasEff.instOp {e : ε} {f : φ} {a : Term φ (Ty α)} [hf : S.FnEff e f] [ha : HasEff e a]
  : HasEff e (.op f a) := HasEff.op hf ha

instance HasEff.instLet₁ {e : ε} {A : Ty α} {a b : Term φ (Ty α)}
  [ha : HasEff e a] [hb : HasEff e b] : HasEff e (.let₁ a A b) := HasEff.let₁ ha hb

instance HasEff.instLet₂ {e : ε} {A B : Ty α} {a b : Term φ (Ty α)}
  [ha : HasEff e a] [hb : HasEff e b] : HasEff e (.let₂ a A B b) := HasEff.let₂ ha hb

instance HasEff.instPair {e : ε} {a b : Term φ (Ty α)} [ha : HasEff e a] [hb : HasEff e b]
  : HasEff e (.pair a b) := HasEff.pair ha hb

instance HasEff.instInl {e : ε} {A B : Ty α} {a : Term φ (Ty α)} [ha : HasEff e a]
  : HasEff e (.inl A B a) := HasEff.inl ha

instance HasEff.instInr {e : ε} {A B : Ty α} {b : Term φ (Ty α)} [hb : HasEff e b]
  : HasEff e (.inr A B b) := HasEff.inr hb

instance HasEff.instCase {e : ε} {A B : Ty α} {a b c : Term φ (Ty α)}
  [ha : HasEff e a] [hb : HasEff e b] [hc : HasEff e c] : HasEff e (.case a A B b c)
  := HasEff.case ha hb hc

instance HasEff.instAbort {e : ε} {A : Ty α} {a : Term φ (Ty α)} [ha : HasEff e a]
  : HasEff e (.abort A a) := HasEff.abort ha

syntax "inductive_and" : tactic

macro_rules
  | `(tactic| inductive_and) => `(tactic| {
    apply Iff.intro
    · intro h; cases h; (repeat first | assumption | constructor)
    · intro h; (try casesm* _ ∧ _); constructor <;> assumption
  })

@[simp]
theorem HasEff.op_iff {e : ε} {f : φ} {a : Term φ (Ty α)}
  : HasEff e (.op f a) ↔ S.FnEff e f ∧ HasEff e a := by inductive_and

theorem HasEff.op_fn {e : ε} {f : φ} {a : Term φ (Ty α)} (h : HasEff e (.op f a))
  : S.FnEff e f := by rw [HasEff.op_iff] at h; exact h.1

theorem HasEff.op_arg {e : ε} {f : φ} {a : Term φ (Ty α)} (h : HasEff e (.op f a))
  : HasEff e a := by rw [HasEff.op_iff] at h; exact h.2

@[simp]
theorem HasEff.let₁_iff {e : ε} {A : Ty α} {a b : Term φ (Ty α)}
  : HasEff e (.let₁ a A b) ↔ HasEff e a ∧ HasEff e b := by inductive_and

theorem HasEff.let₁_bind {e : ε} {A : Ty α} {a b : Term φ (Ty α)} (h : HasEff e (.let₁ a A b))
  : HasEff e a := by rw [HasEff.let₁_iff] at h; exact h.1

theorem HasEff.let₁_body {e : ε} {A : Ty α} {a b : Term φ (Ty α)} (h : HasEff e (.let₁ a A b))
  : HasEff e b := by rw [HasEff.let₁_iff] at h; exact h.2

@[simp]
theorem HasEff.let₂_iff {e : ε} {A B : Ty α} {a b : Term φ (Ty α)}
  : HasEff e (.let₂ a A B b) ↔ HasEff e a ∧ HasEff e b := by inductive_and

theorem HasEff.let₂_bind {e : ε} {A B : Ty α} {a b : Term φ (Ty α)} (h : HasEff e (.let₂ a A B b))
  : HasEff e a := by rw [HasEff.let₂_iff] at h; exact h.1

theorem HasEff.let₂_body {e : ε} {A B : Ty α} {a b : Term φ (Ty α)} (h : HasEff e (.let₂ a A B b))
  : HasEff e b := by rw [HasEff.let₂_iff] at h; exact h.2

@[simp]
theorem HasEff.pair_iff {e : ε} {a b : Term φ (Ty α)}
  : HasEff e (.pair a b) ↔ HasEff e a ∧ HasEff e b := by inductive_and

theorem HasEff.pair_fst {e : ε} {a b : Term φ (Ty α)} (h : HasEff e (.pair a b))
  : HasEff e a := by rw [HasEff.pair_iff] at h; exact h.1

theorem HasEff.pair_snd {e : ε} {a b : Term φ (Ty α)} (h : HasEff e (.pair a b))
  : HasEff e b := by rw [HasEff.pair_iff] at h; exact h.2

@[simp]
theorem HasEff.inl_iff {e : ε} {A B : Ty α} {a : Term φ (Ty α)}
  : HasEff e (.inl A B a) ↔ HasEff e a := by inductive_and

theorem HasEff.inl_arg {e : ε} {A B : Ty α} {a : Term φ (Ty α)} (h : HasEff e (.inl A B a))
  : HasEff e a := by rw [HasEff.inl_iff] at h; exact h

@[simp]
theorem HasEff.inr_iff {e : ε} {A B : Ty α} {b : Term φ (Ty α)}
  : HasEff e (.inr A B b) ↔ HasEff e b := by inductive_and

theorem HasEff.inr_arg {e : ε} {A B : Ty α} {b : Term φ (Ty α)} (h : HasEff e (.inr A B b))
  : HasEff e b := by rw [HasEff.inr_iff] at h; exact h

@[simp]
theorem HasEff.case_iff {e : ε} {A B : Ty α} {a b c : Term φ (Ty α)}
  : HasEff e (.case a A B b c) ↔ HasEff e a ∧ HasEff e b ∧ HasEff e c := by inductive_and

theorem HasEff.case_desc {e : ε} {A B : Ty α} {a b c : Term φ (Ty α)}
  (h : HasEff e (.case a A B b c))
  : HasEff e a := by rw [HasEff.case_iff] at h; exact h.1

theorem HasEff.case_left {e : ε} {A B : Ty α} {a b c : Term φ (Ty α)}
  (h : HasEff e (.case a A B b c))
  : HasEff e b := by rw [HasEff.case_iff] at h; exact h.2.1

theorem HasEff.case_right {e : ε} {A B : Ty α} {a b c : Term φ (Ty α)}
  (h : HasEff e (.case a A B b c))
  : HasEff e c := by rw [HasEff.case_iff] at h; exact h.2.2

@[simp]
theorem HasEff.abort_iff {e : ε} {A : Ty α} {a : Term φ (Ty α)}
  : HasEff e (.abort A a) ↔ HasEff e a := by inductive_and

theorem HasEff.abort_arg {e : ε} {A : Ty α} {a : Term φ (Ty α)} (h : HasEff e (.abort A a))
  : HasEff e a := by rw [HasEff.abort_iff] at h; exact h

@[simp]
theorem HasEff.iter_iff {e : ε} {A B : Ty α} {a b : Term φ (Ty α)}
  : HasEff e (.iter a A B b) ↔ e ∈ S.iterative ∧ HasEff e a ∧ HasEff e b := by inductive_and

theorem HasEff.iter_eff {e : ε} {A B : Ty α} {a b : Term φ (Ty α)} (h : HasEff e (.iter a A B b))
  : e ∈ S.iterative := by rw [HasEff.iter_iff] at h; exact h.1

theorem HasEff.iter_init {e : ε} {A B : Ty α} {a b : Term φ (Ty α)} (h : HasEff e (.iter a A B b))
  : HasEff e a := by rw [HasEff.iter_iff] at h; exact h.2.1

theorem HasEff.iter_body {e : ε} {A B : Ty α} {a b : Term φ (Ty α)} (h : HasEff e (.iter a A B b))
  : HasEff e b := by rw [HasEff.iter_iff] at h; exact h.2.2

@[simp]
theorem HasEff.wk_iff (ρ : ℕ → ℕ) {e : ε} {a : Term φ (Ty α)} : HasEff e (a.ren ρ) ↔ HasEff e a :=
  by induction a generalizing ρ <;> simp [*]

instance HasEff.instWk {e : ε} {a : Term φ (Ty α)} (ρ : ℕ → ℕ) [ha : HasEff e a]
  : HasEff e (a.ren ρ) := by rw [HasEff.wk_iff]; exact ha

theorem HasEff.mono {e e' : ε} (he : e ≤ e') {a : Term φ (Ty α)} (h : HasEff e a) : HasEff e' a :=
  by induction h <;> simp [Signature.FnEff.mono he, S.iterative_is_upper he, *]

instance HasEff.top {a : Term φ (Ty α)} : HasEff ⊤ a := by induction a <;> simp [*]

end Term

end Refinery
