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

theorem Ctx?.IsZero.eq_erase {Γ : Ctx? α} (h : Γ.IsZero) : Γ.erase = Γ := by induction h with
  | nil => rfl
  | cons => simp only [Ctx?.erase_cons, Var?.unused.eq_erase]; congr

variable [HasQuant α]

@[simp]
theorem Ctx?.IsZero.del {Γ : Ctx? α} (h : Γ.IsZero) : Γ.del := by induction h <;> simp [*]

inductive Ctx?.SAt : Var? α → Ctx? α → ℕ → Type _ where
  | here {Γ} (d : Γ.IsZero) {w} : w ≤ v → Ctx?.SAt v (Ctx?.cons Γ w) 0
  | there {Γ n} (x : Ctx?.SAt v Γ n) (A) : Ctx?.SAt v (Ctx?.cons Γ ⟨A, 0⟩) (n + 1)

instance Ctx?.SAt.instSubsingleton {v : Var? α} {Γ : Ctx? α} {n} : Subsingleton (Ctx?.SAt v Γ n)
  where
  allEq x y := by induction x <;> cases y <;> simp; apply_assumption

def Ctx?.SAt.cast {v v' : Var? α} {Γ Γ' : Ctx? α} {n n'}
  (hΓ : Γ = Γ') (hv : v = v') (hn : n = n') (x : Γ.SAt v n)
  : Γ'.SAt v' n' := hΓ ▸ hv ▸ hn ▸ x

@[simp]
theorem Ctx?.SAt.cast_rfl {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.SAt v n)
  : x.cast rfl rfl rfl = x := by rfl

@[simp]
theorem Ctx?.SAt.cast_cast {v v' v'' : Var? α} {Γ Γ' Γ'' : Ctx? α} {n n' n''}
  (hΓ : Γ = Γ') (hv : v = v') (hn : n = n') (hΓ' : Γ' = Γ'') (hv' : v' = v'') (hn' : n' = n'')
  (x : Γ.SAt v n)
  : (x.cast hΓ hv hn).cast hΓ' hv' hn' = x.cast (hΓ.trans hΓ') (hv.trans hv') (hn.trans hn')
  := by cases hΓ'; cases hv'; cases hn'; rfl

abbrev Ctx?.SAt.cast_src {v : Var? α} {Γ Γ' : Ctx? α} {n} (hΓ : Γ = Γ') (x : Γ.SAt v n)
  : Γ'.SAt v n := x.cast hΓ rfl rfl

abbrev Ctx?.SAt.cast_trg {v v' : Var? α} {Γ : Ctx? α} {n} (hv : v = v') (x : Γ.SAt v n)
  : Γ.SAt v' n := x.cast rfl hv rfl

abbrev Ctx?.SAt.cast_idx {v : Var? α} {Γ : Ctx? α} {n n'} (hn : n = n') (x : Γ.SAt v n)
  : Γ.SAt v n' := x.cast rfl rfl hn

@[simp]
theorem Ctx?.SAt.cast_here {v v' : Var? α} {Γ Γ' : Ctx? α} (d : Γ.IsZero)
  {w w' : Var? α} (h : w ≤ v) (hΓ : Γ.cons w = Γ'.cons w') (hv : v = v')
  : (SAt.here d h).cast hΓ hv rfl = .here (by cases hΓ; exact d) (by cases hΓ; cases hv; exact h)
  := by cases hΓ; cases hv; rfl

@[simp]
theorem Ctx?.SAt.cast_there {v v' : Var? α} {Γ Γ' : Ctx? α} {n n'} (x : Γ.SAt v n) (A)
  (hΓ : Γ.cons ⟨A, 0⟩ = Γ'.cons ⟨A', 0⟩) (hv : v = v') (hn : n + 1 = n' + 1)
  : (x.there A).cast hΓ hv hn = (x.cast (by cases hΓ; rfl) hv (by cases hn; rfl)).there A'
  := by cases hΓ; cases hv; cases hn; rfl

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
  | .there (w := w) x hw => x.toUsed.cons (Var?.del_iff_erase_le.mp hw)

@[simp]
def Ctx?.At.strict {v : Var? α} {Γ : Ctx? α} {n} : (x : Γ.At v n) → x.used.SAt v n
  | .here _ hvw => .here (by simp) hvw
  | .there x hw => .there x.strict _

@[simp]
def Ctx?.At.ssplit {v : Var? α} {Γ : Ctx? α} {n} : (x : Γ.At v n) → SSplit Γ x.used x.unused
  | .here (Γ := Γ) (w := w) _ _ => Γ.erase_left.cons (.left w)
  | .there (w := w) x _ => x.ssplit.cons (.right w)

theorem Ctx?.SAt.unstrict_used_eq {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.SAt v n)
  : x.unstrict.used = Γ := by induction x <;> simp [*]; rw [IsZero.eq_erase]; assumption

theorem Ctx?.SAt.strict_unstrict_here {Γ : Ctx? α} (d : Γ.IsZero) {w} (h : w ≤ v)
  : (SAt.here d h).unstrict.strict = (SAt.here d h).cast_src (by simp [d.eq_erase])
  := by simp

theorem Ctx?.SAt.strict_unstrict {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.SAt v n)
  : x.unstrict.strict = x.cast_src (x.unstrict_used_eq.symm) := by induction x <;> simp [*]

theorem Ctx?.SAt.cast_strict_unstrict {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.SAt v n)
  : x.unstrict.strict.cast_src x.unstrict_used_eq = x := by rw [strict_unstrict]; simp
