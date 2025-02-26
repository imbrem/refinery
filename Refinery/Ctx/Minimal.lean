import Refinery.Ctx.Basic
import Refinery.Ctx.SSplit

namespace Refinery

open HasQuant

inductive Ctx?.IsZero : Ctx? α → Prop where
  | nil : IsZero .nil
  | cons {Γ A} (hΓ : IsZero Γ) : IsZero (Ctx?.cons Γ ⟨A, 0⟩)

attribute [simp] Ctx?.IsZero.nil Ctx?.IsZero.cons

inductive Ctx?.TyEq : Ctx? α → Ctx? α → Prop
  | nil : Ctx?.TyEq .nil .nil
  | cons {Γ Δ} {v w} : TyEq Γ Δ → v.ty = w.ty → Ctx?.TyEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)

@[simp]
theorem Ctx?.TyEq.cons_iff {Γ Δ : Ctx? α} {v w}
  : (Γ.cons v).TyEq (Δ.cons w) ↔ Γ.TyEq Δ ∧ v.ty = w.ty
  := ⟨λh => by cases h; simp [*], λ⟨_, _⟩ => by constructor <;> assumption⟩

@[refl, simp]
theorem Ctx?.TyEq.refl (Γ : Ctx? α) : Ctx?.TyEq Γ Γ := by induction Γ <;> simp [nil, *]

@[simp]
theorem Ctx?.TyEq.symm {Γ Δ : Ctx? α} (h : Ctx?.TyEq Γ Δ) : Ctx?.TyEq Δ Γ := by
  induction h <;> simp [*]

theorem Ctx?.TyEq.trans {Γ Δ Ξ : Ctx? α} (hΓΔ : Ctx?.TyEq Γ Δ) (hΔΞ : Ctx?.TyEq Δ Ξ) : Ctx?.TyEq Γ Ξ
  := by induction hΓΔ generalizing Ξ with
  | nil => assumption
  | cons hΓΔ hty =>
    cases hΔΞ; constructor; apply_assumption; assumption; apply Eq.trans <;> assumption

theorem Ctx?.TyEq.length_eq {Γ Δ : Ctx? α} (h : Γ.TyEq Δ) : Γ.length = Δ.length := by
  induction h <;> simp [*]

@[simp]
theorem Ctx?.erase_is_zero {Γ : Ctx? α} : Γ.erase.IsZero := by induction Γ <;> simp [*]

theorem Ctx?.IsZero.eq_erase {Γ : Ctx? α} (h : Γ.IsZero) : Γ.erase = Γ := by induction h with
  | nil => rfl
  | cons => simp only [Ctx?.erase_cons, Var?.unused.eq_erase]; congr

inductive Var?.ZQEq : Var? α → Var? α → Prop
  | refl {u} : ZQEq u u
  | erase_left {v} : ZQEq v.erase v
  | erase_right {v} : ZQEq v v.erase

attribute [refl] Var?.ZQEq.refl
attribute [simp] Var?.ZQEq.refl Var?.ZQEq.erase_left Var?.ZQEq.erase_right

theorem Var?.ZQEq.ty {u v : Var? α} (h : Var?.ZQEq u v) : u.ty = v.ty := by
  cases h <;> rfl

@[simp]
theorem Var?.ZQEq.symm {u v : Var? α} (h : Var?.ZQEq u v) : Var?.ZQEq v u
  := by cases h <;> constructor

inductive Ctx?.ZQEq : Ctx? α → Ctx? α → Prop
  | nil : Ctx?.ZQEq .nil .nil
  | cons {Γ Δ} {v w} : ZQEq Γ Δ → v.ZQEq w → Ctx?.ZQEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)

attribute [simp] Ctx?.ZQEq.nil

@[simp]
theorem Ctx?.ZQEq.cons_iff {Γ Δ : Ctx? α} {v w} : (Γ.cons v).ZQEq (Δ.cons w) ↔ Γ.ZQEq Δ ∧ v.ZQEq w
  := ⟨λh => by cases h; simp [*], λ⟨_, _⟩ => by constructor <;> assumption⟩

@[simp]
theorem Ctx?.ZQEq.refl (Γ : Ctx? α) : Ctx?.ZQEq Γ Γ := by induction Γ <;> simp [*]

@[simp]
theorem Ctx?.ZQEq.erase_left {Γ : Ctx? α} : Ctx?.ZQEq Γ.erase Γ := by induction Γ <;> simp [*]

@[simp]
theorem Ctx?.ZQEq.erase_right {Γ : Ctx? α} : Ctx?.ZQEq Γ Γ.erase := by induction Γ <;> simp [*]

structure Var?.UEq (u v : Var? α) : Prop where
  ty : u.ty = v.ty
  unused : u.unused = v.unused

@[refl, simp]
theorem Var?.UEq.refl (u : Var? α) : Var?.UEq u u := ⟨rfl, rfl⟩

@[simp]
theorem Var?.UEq.symm {u v : Var? α} (h : Var?.UEq u v) : Var?.UEq v u := ⟨h.ty.symm, h.unused.symm⟩

theorem Var?.UEq.trans {u v w : Var? α} (huv : Var?.UEq u v) (hvw : Var?.UEq v w) : Var?.UEq u w
  := ⟨huv.ty.trans hvw.ty, huv.unused.trans hvw.unused⟩

theorem Var?.UEq.ety_eq {u v : Var? α} (h : Var?.UEq u v) : u.ety = v.ety := by
  cases u with | mk A q => cases v with | mk B q' =>
  cases h.ty
  have h := h.unused
  cases q using EQuant.casesZero with
  | zero => simp at h; cases h; rfl
  | rest => cases q' using EQuant.casesZero with
    | zero => simp at h
    | rest => rfl

inductive Ctx?.UEq : Ctx? α → Ctx? α → Prop
  | nil : Ctx?.UEq .nil .nil
  | cons {Γ Δ} {v w} : UEq Γ Δ → v.UEq w → Ctx?.UEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)

attribute [simp] Ctx?.UEq.nil

@[simp]
theorem Ctx?.UEq.cons_iff {Γ Δ : Ctx? α} {v w} : (Γ.cons v).UEq (Δ.cons w) ↔ Γ.UEq Δ ∧ v.UEq w
  := ⟨λh => by cases h; simp [*], λ⟨_, _⟩ => by constructor <;> assumption⟩

@[refl, simp]
theorem Ctx?.UEq.refl (Γ : Ctx? α) : Ctx?.UEq Γ Γ := by induction Γ <;> simp [*]

@[simp]
theorem Ctx?.UEq.symm {Γ Δ : Ctx? α} (h : Ctx?.UEq Γ Δ) : Ctx?.UEq Δ Γ := by
  induction h <;> simp [*]

theorem Ctx?.UEq.trans {Γ Δ Ξ : Ctx? α} (hΓΔ : Ctx?.UEq Γ Δ) (hΔΞ : Ctx?.UEq Δ Ξ) : Ctx?.UEq Γ Ξ
  := by induction hΓΔ generalizing Ξ with
  | nil => assumption
  | cons hΓΔ huv =>
    cases hΔΞ; constructor; apply_assumption; assumption
    apply Var?.UEq.trans <;> assumption

theorem Ctx?.UEq.ty_eq {Γ Δ : Ctx? α} (h : Ctx?.UEq Γ Δ) : Γ.TyEq Δ := by
  induction h <;> constructor; assumption; apply Var?.UEq.ty; assumption

theorem Ctx?.UEq.ety_eq {Γ Δ : Ctx? α} (h : Ctx?.UEq Γ Δ) : Γ.ety = Δ.ety := by
  induction h <;> simp [*]; apply Var?.UEq.ety_eq; assumption

theorem Ctx?.TyEq.zero_ueq {Γ Δ : Ctx? α} (h : Ctx?.TyEq Γ Δ) (hΓ : Γ.IsZero) (hΔ : Δ.IsZero)
  : Γ.UEq Δ := by
  induction h <;> cases hΓ <;> cases hΔ
  rfl
  constructor
  apply_assumption <;> assumption
  constructor; assumption; rfl

variable [HasQuant α]

theorem Ctx?.SSplit.left_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Γ.TyEq Δ := by
  induction σ <;> simp [*]; apply Var?.SSplit.left_ty_eq; assumption

theorem Ctx?.SSplit.right_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Γ.TyEq Ξ := by
  induction σ <;> simp [*]; apply Var?.SSplit.right_ty_eq; assumption

theorem Ctx?.SSplit.out_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Δ.TyEq Ξ := by
  induction σ <;> simp [*]; rename_i h _; cases h <;> rfl

theorem Var?.SSplit.in_ueq {u v w u' v' w' : Var? α} (σ : u.SSplit v w) (σ' : u'.SSplit v' w')
  (hv : v.UEq v') (hw : w.UEq w') : u.UEq u' := by
  cases u with | mk A q => cases u' with | mk A' q' =>
  cases σ <;> cases σ' <;> (try simp [*]) <;> cases hv.ty
  <;> { have hv := hv.unused; simp at *; cases hv; exact ⟨rfl, hw.unused⟩ }

theorem Ctx?.SSplit.in_ueq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α} (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ')
  (hΔ : Δ.UEq Δ') (hΞ : Ξ.UEq Ξ') : Γ.UEq Γ' := by
  induction σ generalizing Γ' Δ' Ξ' with
  | nil => cases σ'; constructor; cases hΔ
  | cons σ h I => cases σ' with
    | nil => cases hΔ
    | cons σ' h' =>
      simp at *; casesm* _ ∧ _
      constructor; apply I <;> assumption
      apply Var?.SSplit.in_ueq <;> assumption

theorem Var?.SSplit.zqeq_left {u v w : Var? α} (σ : u.SSplit v w) : u.ZQEq w := by
  cases σ <;> constructor

theorem Var?.SSplit.zqeq_right {u v w : Var? α} (σ : u.SSplit v w) : u.ZQEq v := by
  cases σ <;> constructor

theorem Var?.SSplit.zqeq_out {u v w : Var? α} (σ : u.SSplit v w) : v.ZQEq w := by
  cases σ <;> constructor

@[simp]
theorem Ctx?.IsZero.del {Γ : Ctx? α} (h : Γ.IsZero) : Γ.del := by induction h <;> simp [*]

inductive Ctx?.SAt : Var? α → Ctx? α → ℕ → Type _ where
  | here {Γ} (d : Γ.IsZero) {w} : w ≤ v → Ctx?.SAt v (Ctx?.cons Γ w) 0
  | there {Γ n} (x : Ctx?.SAt v Γ n) (A) : Ctx?.SAt v (Ctx?.cons Γ ⟨A, 0⟩) (n + 1)

theorem Ctx?.SAt.ueq_of_ty_eq {v : Var? α} {Γ Γ' : Ctx? α} {n} (hΓ : Γ.TyEq Γ')
  (x : Γ.SAt v n) (x' : Γ'.SAt v n) (hv : v.used) : Γ.UEq Γ'
  := by
  induction hΓ generalizing v n with
  | nil => cases x
  | cons h hA I =>
    rename_i w w';
    cases v with | mk Av qv =>
    cases w with | mk Aw qw =>
    cases w' with | mk Aw' qw' =>
    cases hA
    cases x <;> cases x'
    constructor; apply TyEq.zero_ueq <;> assumption; constructor;
    apply Eq.trans
    apply Var?.Wk.ty; assumption
    apply Eq.symm; apply Var?.Wk.ty; assumption
    cases qw using EQuant.casesZero with
    | zero => cases qw' using EQuant.casesZero with
      | zero => rfl
      | rest =>
        rename_i he qq he'
        cases Var?.Wk.zero_le_unused he
        cases hv
    | rest => cases qw' using EQuant.casesZero with
      | zero =>
        rename_i he qq he'
        cases Var?.Wk.zero_le_unused he'
        cases hv
      | rest => simp
    constructor; apply_assumption <;> assumption; rfl

theorem Ctx?.SAt.ty_eq_out {v v' : Var? α} {Γ Γ' : Ctx? α} {n}  (hΓ : Γ.TyEq Γ')
  (x : Γ.SAt v n) (x' : Γ'.SAt v' n) : v.ty = v'.ty := by
  induction x generalizing Γ' <;> cases x'
  · cases hΓ with | cons _ h => rename_i w2 _ _ _ w1 _; rw [<-w2.ty, <-w1.ty, h]
  · apply_assumption; simp at hΓ; exact hΓ.left; assumption

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
