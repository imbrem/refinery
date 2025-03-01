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

theorem Ctx?.TyEq.tail {Γ Δ : Ctx? α} {v w}
  (h : Ctx?.TyEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)) : Γ.TyEq Δ
  := by cases h; assumption

theorem Ctx?.TyEq.head {Γ Δ : Ctx? α} {v w}
  (h : Ctx?.TyEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)) : v.ty = w.ty
  := by cases h; assumption

theorem Ctx?.TyEq.length_eq {Γ Δ : Ctx? α} (h : Γ.TyEq Δ) : Γ.length = Δ.length := by
  induction h <;> simp [*]

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

@[simp]
theorem Var?.ZQEq.zero_right {A : Ty α} {q} : ZQEq ⟨A, q⟩ ⟨A, 0⟩ := ZQEq.erase_right

@[simp]
theorem Var?.ZQEq.zero_left {A : Ty α} {q} : ZQEq ⟨A, 0⟩ ⟨A, q⟩ := ZQEq.erase_left (v := ⟨A, q⟩)

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

theorem Ctx?.ZQEq.tail {Γ Δ : Ctx? α} {v w}
  (h : Ctx?.ZQEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)) : Γ.ZQEq Δ
  := by cases h; assumption

theorem Ctx?.ZQEq.head {Γ Δ : Ctx? α} {v w}
  (h : Ctx?.ZQEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)) : v.ZQEq w
  := by cases h; assumption

theorem Ctx?.ZQEq.length_eq {Γ Δ : Ctx? α} (h : Γ.ZQEq Δ) : Γ.length = Δ.length := by
  induction h <;> simp [*]

@[simp, refl]
theorem Ctx?.ZQEq.refl (Γ : Ctx? α) : Ctx?.ZQEq Γ Γ := by induction Γ <;> simp [*]

@[simp]
theorem Ctx?.ZQEq.erase_left {Γ : Ctx? α} : Ctx?.ZQEq Γ.erase Γ := by induction Γ <;> simp [*]

@[simp]
theorem Ctx?.ZQEq.erase_right {Γ : Ctx? α} : Ctx?.ZQEq Γ Γ.erase := by induction Γ <;> simp [*]

theorem Ctx?.ZQEq.ty_eq {Γ Δ : Ctx? α} (h : Ctx?.ZQEq Γ Δ) : Γ.TyEq Δ := by
  induction h <;> constructor; assumption; apply Var?.ZQEq.ty; assumption

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

theorem Ctx?.UEq.tail {Γ Δ : Ctx? α} {v w}
  (h : Ctx?.UEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)) : Γ.UEq Δ
  := by cases h; assumption

theorem Ctx?.UEq.head {Γ Δ : Ctx? α} {v w}
  (h : Ctx?.UEq (Ctx?.cons Γ v) (Ctx?.cons Δ w)) : v.UEq w
  := by cases h; assumption

theorem Ctx?.UEq.length_eq {Γ Δ : Ctx? α} (h : Γ.UEq Δ) : Γ.length = Δ.length := by
  induction h <;> simp [*]

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

theorem Var?.ZQEq.ueq {u v : Var? α} (h : Var?.ZQEq u v) (h' : Var?.UEq u v) : u = v
  := by cases u with | mk A qu => cases v with | mk B qv => cases h with
  | refl => rfl
  | _ => have h' := h'.unused; simp at h'; cases h'; rfl

theorem Ctx?.ZQEq.ueq {Γ Δ : Ctx? α} (h : Ctx?.ZQEq Γ Δ) (h' : Ctx?.UEq Γ Δ) : Γ = Δ
  := by induction h with
  | nil => rfl
  | cons h hv I => cases h' with | cons h' hv' => rw [I h', hv.ueq hv']

theorem Var?.UEq.zqeq {u v : Var? α} (h : Var?.UEq u v) (h' : Var?.ZQEq u v) : u = v
  := h'.ueq h

theorem Ctx?.UEq.zqeq {Γ Δ : Ctx? α} (h : Ctx?.UEq Γ Δ) (h' : Ctx?.ZQEq Γ Δ) : Γ = Δ
  := h'.ueq h

variable [HasQuant α]

inductive Var?.ZWk : Var? α → Var? α → Type _ where
  | refl (u) : Var?.ZWk u u
  | erase {A q} (h : Var?.del ⟨A, q⟩) : Var?.ZWk ⟨A, q⟩ ⟨A, 0⟩

attribute [refl] Var?.ZWk.refl

theorem Var?.ZWk.ty {u v : Var? α} (h : Var?.ZWk u v) : u.ty = v.ty := by
  cases h <;> rfl

theorem Var?.ZWk.toWk {u v : Var? α} : (ρ : u.ZWk v) → u.Wk v
  | .refl u => le_refl u
  | .erase h => h.erase_le

def Var?.ZWk.comp {u v w : Var? α} : u.ZWk v → v.ZWk w → u.ZWk w
  | .refl _, ρ => ρ
  | .erase h, .refl _ => .erase h
  | .erase h, .erase h' => .erase h

@[simp]
theorem Var?.ZWk.zqeq {u v : Var? α} (ρ : u.ZWk v) : u.ZQEq v := by cases ρ <;> simp [*]

theorem Var?.ZWk.copy {u v : Var? α} (ρ : u.ZWk v) [hu : u.copy] : v.copy := by
  cases ρ <;> infer_instance

theorem Var?.ZWk.del {u v : Var? α} (ρ : u.ZWk v) [hu : u.del] : v.del := by
  cases ρ <;> infer_instance

inductive Ctx?.ZWk : Ctx? α → Ctx? α → Type _ where
  | nil : Ctx?.ZWk .nil .nil
  | cons {Γ Δ} {v w} (h : Ctx?.ZWk Γ Δ) (hv : v.ZWk w)
    : Ctx?.ZWk (Ctx?.cons Γ v) (Ctx?.cons Δ w)

@[simp, refl]
def Ctx?.ZWk.refl : (Γ : Ctx? α) → ZWk Γ Γ
  | .nil => .nil
  | .cons Γ v => .cons (refl Γ) (.refl v)

@[simp]
def Ctx?.ZWk.toPWk {Γ Δ : Ctx? α} : ZWk Γ Δ → PWk Γ Δ
  | .nil => .nil
  | .cons ρ v => .cons (toPWk ρ) v.toWk

@[simp]
def Ctx?.ZWk.comp {Γ Δ Ξ : Ctx? α} : ZWk Γ Δ → ZWk Δ Ξ → ZWk Γ Ξ
  | .nil, .nil => .nil
  | .cons ρ h, .cons ρ' h' => .cons (comp ρ ρ') (h.comp h')

@[simp]
theorem Ctx?.ZWk.toPWk_refl {Γ : Ctx? α} : (ZWk.refl Γ).toPWk = PWk.refl Γ := by
  induction Γ <;> simp [*]

def Ctx?.ZWk.tail {Γ Δ : Ctx? α} {v}
  : Ctx?.ZWk (Ctx?.cons Γ v) Δ → Ctx?.ZWk Γ Δ.tail
  | .cons ρ _ => ρ

instance Ctx?.ZWk.coePWk {Γ Δ : Ctx? α} : Coe (Ctx?.ZWk Γ Δ) (Ctx?.PWk Γ Δ) := ⟨Ctx?.ZWk.toPWk⟩

theorem Ctx?.ZWk.copy {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) [hΓ : Γ.copy] : Δ.copy := by
  generalize hΓ = hΓ
  induction ρ with
  | nil => infer_instance
  | cons ρ h ih => simp [*] at *; cases hΓ; constructor; apply ih; assumption; apply h.copy

theorem Ctx?.ZWk.del {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) [hΓ : Γ.del] : Δ.del := by
  generalize hΓ = hΓ
  induction ρ with
  | nil => infer_instance
  | cons ρ h ih => simp [*] at *; cases hΓ; constructor; apply ih; assumption; apply h.del

@[simp]
theorem Ctx?.ZWk.zqeq {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) : Γ.ZQEq Δ
  := by induction ρ <;> simp [*]; apply Var?.ZWk.zqeq; assumption

theorem Ctx?.ZWk.antisymm  {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) (σ : Δ.ZWk Γ) : Γ = Δ := PWk.antisymm ρ σ

def Var?.SSplit.fuseCtx {u v w v' w' : Var? α} : u.SSplit v w → v.ZWk v' → w.ZWk w' → Var? α
  | .left _, .refl _, _ => u
  | .left _, .erase _, _ => u.erase
  | .right _, _, .refl _ => u
  | .right _, _, .erase _ => u.erase
  | .sboth _, .erase _, .erase _ => u.erase
  | .sboth _, _, _ => u

def Var?.SSplit.fuse {u v w v' w' : Var? α} :
  (σ : u.SSplit v w) → (ρ : v.ZWk v') → (ρ' : w.ZWk w') → (σ.fuseCtx ρ ρ').SSplit v' w'
  | .left _, .refl _, .refl _ => .left _
  | .left _, .refl _, .erase _ => .left _
  | .left _, .erase _, .refl _ => .left _
  | .left _, .erase _, .erase _ => .left _
  | .right _, .refl _, .refl _ => .right _
  | .right _, .refl _, .erase _ => .right _
  | .right _, .erase _, .refl _ => .right _
  | .right _, .erase _, .erase _ => .right _
  | .sboth _, .erase _, .erase _ => .left _
  | .sboth _, .refl _, .erase _ => .left _
  | .sboth _, .erase _, .refl _ => .right _
  | .sboth h, .refl _, .refl _ => .sboth h

def Var?.SSplit.fuseWk {u v w v' w' : Var? α} :
  (σ : u.SSplit v w) → (ρ : v.ZWk v') → (ρ' : w.ZWk w') → u.ZWk (σ.fuseCtx ρ ρ')
  | .left _, .refl _, _ => .refl _
  | .left _, .erase h, _ => .erase h
  | .right _, _, .refl _ => .refl _
  | .right _, _, .erase h => .erase h
  | .sboth _, .refl _, .refl _
  | .sboth _, .refl _, .erase _ => .refl _
  | .sboth _, .erase _, .refl _ => .refl _
  | .sboth _, .erase _, .erase h => .erase h

def Ctx?.SSplit.fuseCtx {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  : Γ.SSplit Δ Ξ → Δ.ZWk Δ' → Ξ.ZWk Ξ' → Ctx? α
  | .nil, .nil, .nil => .nil
  | .cons σ hvw, .cons ρ h, .cons ρ' h' => (σ.fuseCtx ρ ρ').cons (hvw.fuseCtx h h')

def Ctx?.SSplit.fuse {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  : (σ : Γ.SSplit Δ Ξ) → (ρ : Δ.ZWk Δ') → (ρ' : Ξ.ZWk Ξ') → (σ.fuseCtx ρ ρ').SSplit Δ' Ξ'
  | .nil, .nil, .nil => .nil
  | .cons σ hvw, .cons ρ h, .cons ρ' h' => (σ.fuse ρ ρ').cons (hvw.fuse h h')

def Ctx?.SSplit.fuseWk {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  : (σ : Γ.SSplit Δ Ξ) → (ρ : Δ.ZWk Δ') → (ρ' : Ξ.ZWk Ξ') → Γ.ZWk (σ.fuseCtx ρ ρ')
  | .nil, .nil, .nil => .nil
  | .cons σ hvw, .cons ρ h, .cons ρ' h' => (σ.fuseWk ρ ρ').cons (hvw.fuseWk h h')

theorem Ctx?.At.ty_eq_of {v v' : Var? α} {Γ Γ' : Ctx? α} {n}
  (hΓ : Γ.TyEq Γ') (x : Γ.At v n) (x' : Γ'.At v' n) : v.ty = v'.ty := by
  induction x generalizing Γ' v' with
  | here _ hw => cases x' with | here _ hw' => rw [<-hw.ty, <-hw'.ty, hΓ.head]
  | there => cases x'; apply_assumption; exact hΓ.tail; assumption

theorem Ctx?.SSplit.left_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Γ.TyEq Δ := by
  induction σ <;> simp [*]; apply Var?.SSplit.left_ty_eq; assumption

theorem Ctx?.SSplit.right_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Γ.TyEq Ξ := by
  induction σ <;> simp [*]; apply Var?.SSplit.right_ty_eq; assumption

theorem Ctx?.SSplit.out_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Δ.TyEq Ξ := by
  induction σ <;> simp [*]; rename_i h _; cases h <;> rfl

theorem Ctx?.SSplit.shunt_left_ty_eq  {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ') (hΓ : Γ.TyEq Γ')
  : Δ.TyEq Δ' := σ.left_ty_eq.symm.trans <| hΓ.trans <| σ'.left_ty_eq

theorem Ctx?.SSplit.shunt_right_ty_eq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ') (hΓ : Γ.TyEq Γ')
  : Ξ.TyEq Ξ' := σ.right_ty_eq.symm.trans <| hΓ.trans <| σ'.right_ty_eq

theorem Ctx?.SSplit.pull_left_ty_eq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ') (hΔ : Δ.TyEq Δ')
  : Γ.TyEq Γ' := σ.left_ty_eq.trans <| hΔ.trans <| σ'.left_ty_eq.symm

theorem Ctx?.SSplit.pull_right_ty_eq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ') (hΞ : Ξ.TyEq Ξ')
  : Γ.TyEq Γ' := σ.right_ty_eq.trans <| hΞ.trans <| σ'.right_ty_eq.symm

theorem Ctx?.SSplit.ty_eq_iff_left {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ')
  : Γ.TyEq Γ' ↔ Δ.TyEq Δ' := ⟨σ.shunt_left_ty_eq σ', σ.pull_left_ty_eq σ'⟩

theorem Ctx?.SSplit.ty_eq_iff_right {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ')
  : Γ.TyEq Γ' ↔ Ξ.TyEq Ξ' := ⟨σ.shunt_right_ty_eq σ', σ.pull_right_ty_eq σ'⟩

theorem Ctx?.SSplit.ty_eq_out_iff {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ'.SSplit Δ' Ξ')
  : Δ.TyEq Δ' ↔ Ξ.TyEq Ξ' := by rw [<-σ.ty_eq_iff_left σ', <-σ.ty_eq_iff_right σ']

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

theorem Ctx?.SSplit.zqeq_left {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Γ.ZQEq Ξ := by
  induction σ <;> simp [*]; apply Var?.SSplit.zqeq_left; assumption

theorem Ctx?.SSplit.zqeq_right {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Γ.ZQEq Δ := by
  induction σ <;> simp [*]; apply Var?.SSplit.zqeq_right; assumption

theorem Ctx?.SSplit.zqeq_out {Γ Δ Ξ : Ctx? α} (σ : Γ.SSplit Δ Ξ) : Δ.ZQEq Ξ := by
  induction σ <;> simp [*]; apply Var?.SSplit.zqeq_out; assumption

theorem Var?.SSplit.zqeq_left_of_eq {u v w v' w' : Var? α} (σ : u.SSplit v w) (σ' : u.SSplit v' w')
  : v.ZQEq v' := by
  cases σ <;> cases σ' <;> simp

theorem Var?.SSplit.zqeq_right_of_eq {u v w v' w' : Var? α} (σ : u.SSplit v w) (σ' : u.SSplit v' w')
  : w.ZQEq w' := by
  cases σ <;> cases σ' <;> simp

theorem Ctx?.SSplit.zqeq_left_of_eq  {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ.SSplit Δ' Ξ')
  : Δ.ZQEq Δ' := by
  induction σ generalizing Δ' Ξ' with
  | nil => cases σ'; constructor
  | cons σ h I => cases σ' with
  | cons σ' h' =>
    constructor
    apply I σ'
    apply h.zqeq_left_of_eq h'

theorem Ctx?.SSplit.zqeq_right_of_eq {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  (σ : Γ.SSplit Δ Ξ) (σ' : Γ.SSplit Δ' Ξ')
  : Ξ.ZQEq Ξ' := by
  induction σ generalizing Δ' Ξ' with
  | nil => cases σ'; constructor
  | cons σ h I => cases σ' with
  | cons σ' h' =>
    constructor
    apply I σ'
    apply h.zqeq_right_of_eq h'

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

def Ctx?.eraseZWk (Γ : Ctx? α) [h : Γ.del] : Γ.ZWk Γ.erase := match Γ, h with
  | .nil, _ => .nil
  | .cons Γ _, h => .cons (Γ.eraseZWk (h := h.tail)) (.erase h.head)

@[simp]
def Ctx?.At.toUsed {v : Var? α} {Γ : Ctx? α} {n} : (x : Γ.At v n) → Γ.ZWk x.used
  | .here (Γ := Γ) _ hvw => Γ.eraseZWk.cons (.refl _)
  | .there (w := w) x hw => x.toUsed.cons (.erase hw)

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

inductive Var?.MSplit : Var? α → Var? α → Var? α → Type _
  | left {A q} (h : Var?.del ⟨A, q⟩) : MSplit ⟨A, q⟩ ⟨A, q⟩ ⟨A, 0⟩
  | right {A q} (h : Var?.del ⟨A, q⟩) : MSplit ⟨A, q⟩ ⟨A, 0⟩ ⟨A, q⟩
  | both (A q) : MSplit ⟨A, q⟩ ⟨A, q⟩ ⟨A, q⟩

def Var?.MSplit.zwkLeft {u v w : Var? α} : u.MSplit v w → u.ZWk v
  | .right h => .erase h
  | .both _ _ | .left _  => .refl _

def Var?.MSplit.zwkRight {u v w : Var? α} : u.MSplit v w → u.ZWk w
  | .left h => .erase h
  | .both _ _ | .right _ => .refl _

theorem Var?.MSplit.left_ty_eq {u v w : Var? α} (σ : u.MSplit v w) : u.ty = v.ty := by
  cases σ <;> rfl

theorem Var?.MSplit.right_ty_eq {u v w : Var? α} (σ : u.MSplit v w) : u.ty = w.ty := by
  cases σ <;> rfl

theorem Var?.MSplit.out_ty_eq {u v w : Var? α} (σ : u.MSplit v w) : v.ty = w.ty := by
  cases σ <;> rfl

inductive Ctx?.MSplit : Ctx? α → Ctx? α → Ctx? α → Type _
  | nil : MSplit .nil .nil .nil
  | cons {Γ Δ Ξ} {u v w : Var? α} (σ : MSplit Γ Δ Ξ) (hvw : u.MSplit v w)
    : MSplit (Ctx?.cons Γ u) (Ctx?.cons Δ v) (Ctx?.cons Ξ w)

theorem Ctx?.MSplit.left_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.MSplit Δ Ξ) : Γ.TyEq Δ := by
  induction σ <;> simp [*]; apply Var?.MSplit.left_ty_eq; assumption

theorem Ctx?.MSplit.right_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.MSplit Δ Ξ) : Γ.TyEq Ξ := by
  induction σ <;> simp [*]; apply Var?.MSplit.right_ty_eq; assumption

theorem Ctx?.MSplit.out_ty_eq {Γ Δ Ξ : Ctx? α} (σ : Γ.MSplit Δ Ξ) : Δ.TyEq Ξ := by
  induction σ <;> simp [*]; apply Var?.MSplit.out_ty_eq; assumption

theorem Ctx?.MSplit.shunt_left_ty_eq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ' Ξ') (hΓ : Γ.TyEq Γ')
  : Δ.TyEq Δ' := σ.left_ty_eq.symm.trans <| hΓ.trans <| σ'.left_ty_eq

theorem Ctx?.MSplit.shunt_right_ty_eq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ' Ξ') (hΓ : Γ.TyEq Γ')
  : Ξ.TyEq Ξ' := σ.right_ty_eq.symm.trans <| hΓ.trans <| σ'.right_ty_eq

theorem Ctx?.MSplit.pull_left_ty_eq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ' Ξ') (hΔ : Δ.TyEq Δ')
  : Γ.TyEq Γ' := σ.left_ty_eq.trans <| hΔ.trans <| σ'.left_ty_eq.symm

theorem Ctx?.MSplit.pull_right_ty_eq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ' Ξ') (hΞ : Ξ.TyEq Ξ')
  : Γ.TyEq Γ' := σ.right_ty_eq.trans <| hΞ.trans <| σ'.right_ty_eq.symm

theorem Ctx?.MSplit.ty_eq_iff_left {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ' Ξ')
  : Γ.TyEq Γ' ↔ Δ.TyEq Δ' := ⟨σ.shunt_left_ty_eq σ', σ.pull_left_ty_eq σ'⟩

theorem Ctx?.MSplit.ty_eq_iff_right {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ' Ξ')
  : Γ.TyEq Γ' ↔ Ξ.TyEq Ξ' := ⟨σ.shunt_right_ty_eq σ', σ.pull_right_ty_eq σ'⟩

theorem Var?.MSplit.in_ueq {u v w u' v' w' : Var? α} (σ : u.MSplit v w) (σ' : u'.MSplit v' w')
  (hv : v.UEq v') (hw : w.UEq w') : u.UEq u' := by
  cases u with | mk A q => cases u' with | mk A' q' =>
  cases σ <;> cases σ' <;> (try simp [*]) <;> cases hv.ty
  <;> { have hv := hv.unused; simp at *; cases hv; exact ⟨rfl, hw.unused⟩ }

theorem Ctx?.MSplit.in_ueq {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α} (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ' Ξ')
  (hΔ : Δ.UEq Δ') (hΞ : Ξ.UEq Ξ') : Γ.UEq Γ' := by
  induction σ generalizing Γ' Δ' Ξ' with
  | nil => cases σ'; constructor; cases hΔ
  | cons σ h I => cases σ' with
    | nil => cases hΔ
    | cons σ' h' =>
      simp at *; casesm* _ ∧ _
      constructor; apply I <;> assumption
      apply Var?.MSplit.in_ueq <;> assumption

theorem Var?.MSplit.zqeq_left {u v w : Var? α} (σ : u.MSplit v w) : u.ZQEq w := by
  cases σ <;> constructor

theorem Var?.MSplit.zqeq_right {u v w : Var? α} (σ : u.MSplit v w) : u.ZQEq v := by
  cases σ <;> constructor

theorem Var?.MSplit.zqeq_out {u v w : Var? α} (σ : u.MSplit v w) : v.ZQEq w := by
  cases σ with | right => rename_i A q _; apply ZQEq.erase_left (v := ⟨A, q⟩) | _ => constructor

theorem Ctx?.MSplit.zqeq_left {Γ Δ Ξ : Ctx? α} (σ : Γ.MSplit Δ Ξ) : Γ.ZQEq Ξ := by
  induction σ <;> simp [*]; apply Var?.MSplit.zqeq_left; assumption

theorem Ctx?.MSplit.zqeq_right {Γ Δ Ξ : Ctx? α} (σ : Γ.MSplit Δ Ξ) : Γ.ZQEq Δ := by
  induction σ <;> simp [*]; apply Var?.MSplit.zqeq_right; assumption

theorem Ctx?.MSplit.zqeq_out {Γ Δ Ξ : Ctx? α} (σ : Γ.MSplit Δ Ξ) : Δ.ZQEq Ξ := by
  induction σ <;> simp [*]; apply Var?.MSplit.zqeq_out; assumption

theorem Var?.MSplit.in_eq {u v w u' : Var? α} (σ : u.MSplit v w) (σ' : u'.MSplit v w) : u = u' := by
  cases σ <;> cases σ' <;> rfl

theorem Ctx?.MSplit.in_eq {Γ Δ Ξ Γ' : Ctx? α} (σ : Γ.MSplit Δ Ξ) (σ' : Γ'.MSplit Δ Ξ) : Γ = Γ'
  := by induction σ generalizing Γ' with
  | nil => cases σ'; rfl
  | cons σΓ σv I => cases σ'; rw [I, σv.in_eq] <;> assumption

def Ctx?.MSplit.zwkLeft {Γ Δ Ξ : Ctx? α}
  : Γ.MSplit Δ Ξ → Γ.ZWk Δ
  | .nil => .nil
  | .cons σ hvw => .cons σ.zwkLeft hvw.zwkLeft

def Ctx?.MSplit.zwkRight {Γ Δ Ξ : Ctx? α}
  : Γ.MSplit Δ Ξ → Γ.ZWk Ξ
  | .nil => .nil
  | .cons σ hvw => .cons σ.zwkRight hvw.zwkRight

def Var?.MSplit.fuseCtx {u v w v' w' : Var? α} : u.MSplit v w → v.ZWk v' → w.ZWk w' → Var? α
  | .left _, .refl _, _ => u
  | .left _, .erase _, _ => u.erase
  | .right _, _, .refl _ => u
  | .right _, _, .erase _ => u.erase
  | .both _ _, .erase _, .erase _ => u.erase
  | .both _ _, _, _ => u

def Ctx?.MSplit.fuseCtx {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  : Γ.MSplit Δ Ξ → Δ.ZWk Δ' → Ξ.ZWk Ξ' → Ctx? α
  | .nil, .nil, .nil => .nil
  | .cons σ hvw, .cons ρ h, .cons ρ' h' => (σ.fuseCtx ρ ρ').cons (hvw.fuseCtx h h')

def Var?.MSplit.fuse {u v w v' w' : Var? α} :
  (σ : u.MSplit v w) → (ρ : v.ZWk v') → (ρ' : w.ZWk w') → (σ.fuseCtx ρ ρ').MSplit v' w'
  | .left _, .refl _, .refl _ => .left inferInstance
  | .left _, .refl _, .erase _ => .left inferInstance
  | .left _, .erase _, .refl _ => .left inferInstance
  | .left _, .erase _, .erase _ => .left inferInstance
  | .right _, .refl _, .refl _ => .right inferInstance
  | .right _, .refl _, .erase h => .right inferInstance
  | .right _, .erase h, .refl _ => .right inferInstance
  | .right _, .erase h, .erase _ => .right inferInstance
  | .both _ _, .erase _, .erase _ => .both _ _
  | .both _ _, .refl _, .erase h => .left inferInstance
  | .both _ _, .erase h, .refl _ => .right inferInstance
  | .both _ _, .refl _, .refl _ => .both _ _

def Var?.MSplit.fuseWk {u v w v' w' : Var? α} :
  (σ : u.MSplit v w) → (ρ : v.ZWk v') → (ρ' : w.ZWk w') → u.ZWk (σ.fuseCtx ρ ρ')
  | .left _, .refl _, _ => .refl _
  | .left _, .erase h, _ => .erase h
  | .right _, _, .refl _ => .refl _
  | .right _, _, .erase h => .erase h
  | .both _ _, .erase _, .erase h => .erase h
  | .both _ _, .refl _, .refl _ => .refl _
  | .both h _, .refl _, .erase _ => .refl _
  | .both h _, .erase _, .refl _ => .refl _

def Ctx?.MSplit.fuse {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  : (σ : Γ.MSplit Δ Ξ) → (ρ : Δ.ZWk Δ') → (ρ' : Ξ.ZWk Ξ') → (σ.fuseCtx ρ ρ').MSplit Δ' Ξ'
  | .nil, .nil, .nil => .nil
  | .cons σ hvw, .cons ρ h, .cons ρ' h' => (σ.fuse ρ ρ').cons (hvw.fuse h h')

def Ctx?.MSplit.fuseWk {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  : (σ : Γ.MSplit Δ Ξ) → (ρ : Δ.ZWk Δ') → (ρ' : Ξ.ZWk Ξ') → Γ.ZWk (σ.fuseCtx ρ ρ')
  | .nil, .nil, .nil => .nil
  | .cons σ hvw, .cons ρ h, .cons ρ' h' => (σ.fuseWk ρ ρ').cons (hvw.fuseWk h h')

def Ctx?.bothMSplit : (Γ : Ctx? α) → Γ.MSplit Γ Γ
  | .nil => .nil
  | .cons Γ _ => .cons (bothMSplit Γ) (.both _ _)

def Ctx?.ZWk.mSplitCtx {Γ Δ Ξ : Ctx? α} (ρ : Γ.ZWk Δ) (ρ' : Γ.ZWk Ξ) : Ctx? α
  := Γ.bothMSplit.fuseCtx ρ ρ'

def Ctx?.ZWk.toMSplit {Γ Δ Ξ : Ctx? α} (ρ : Γ.ZWk Δ) (ρ' : Γ.ZWk Ξ) : (ρ.mSplitCtx ρ').MSplit Δ Ξ
  := Γ.bothMSplit.fuse ρ ρ'

def Ctx?.ZWk.wkMSplit {Γ Δ Ξ : Ctx? α} (ρ : Γ.ZWk Δ) (ρ' : Γ.ZWk Ξ) : Γ.ZWk (ρ.mSplitCtx ρ')
  := Γ.bothMSplit.fuseWk ρ ρ'

theorem Var?.ZWk.shunt_zqeq {u v w : Var? α} (h : u.ZWk v) (h' : u.ZWk w) : v.ZQEq w
  := by cases h <;> cases h' <;> simp

theorem Ctx?.ZWk.shunt_zqeq {Γ Δ Ξ : Ctx? α} (h : Γ.ZWk Δ) (h' : Γ.ZWk Ξ) : Δ.ZQEq Ξ
  := by induction h generalizing Ξ with
  | nil => cases h'; constructor
  | cons h t I =>
    cases h'; constructor; apply I; assumption; apply Var?.ZWk.shunt_zqeq <;> assumption

theorem Var?.MSplit.zqeq_left_of_eq {u v w v' w' : Var? α} (σ : u.MSplit v w) (σ' : u.MSplit v' w')
  : v.ZQEq v' := σ.zwkLeft.shunt_zqeq σ'.zwkLeft

theorem Var?.MSplit.zqeq_right_of_eq {u v w v' w' : Var? α} (σ : u.MSplit v w) (σ' : u.MSplit v' w')
  : w.ZQEq w' := σ.zwkRight.shunt_zqeq σ'.zwkRight

theorem Ctx?.MSplit.zqeq_left_of_eq  {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ.MSplit Δ' Ξ')
  : Δ.ZQEq Δ' := σ.zwkLeft.shunt_zqeq σ'.zwkLeft

theorem Ctx?.MSplit.zqeq_right_of_eq {Γ Δ Ξ Δ' Ξ' : Ctx? α}
  (σ : Γ.MSplit Δ Ξ) (σ' : Γ.MSplit Δ' Ξ')
  : Ξ.ZQEq Ξ' := σ.zwkRight.shunt_zqeq σ'.zwkRight
