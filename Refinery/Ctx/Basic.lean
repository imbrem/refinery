import Refinery.Ty
import Discretion.Wk.Nat

namespace Refinery

universe u v

structure Var? (α : Type u) where
  ty : Ty α
  q : EQuant

abbrev Var?.erase (v : Var? α) : Var? α := ⟨v.ty, 0⟩

@[simp]
theorem Var?.erase_erase (v : Var? α) : v.erase.erase = v.erase := rfl

@[simp]
abbrev ety_var {α : Type u} (a : Ty α) : EQuant → Ty α
  | 0 => .unit
  | (q : Quant) => a

abbrev Var?.ety (v : Var? α) : Ty α := ety_var v.ty v.q

theorem Var?.ety_quant_zero {A : Ty α} : Var?.ety ⟨A, 0⟩ = Ty.unit := rfl

theorem Var?.ety_quant_ty {A : Ty α} {q : Quant} : Var?.ety ⟨A, q⟩ = A := rfl

theorem Var?.ety_erase {v : Var? α} : v.erase.ety = Ty.unit := rfl

def Var?.casesZero {motive : Var? α → Sort _} (v : Var? α)
  (zero : ∀A, motive ⟨A, 0⟩)
  (rest : ∀A, ∀q: Quant, motive ⟨A, q⟩) : motive v := match v with
  | ⟨A, 0⟩ => zero A
  | ⟨A, (q : Quant)⟩ => rest A q

def Ctx? (α : Type u) := List (Var? α)

variable {α : Type u} {ε : Type v}

@[match_pattern]
def Ctx?.nil : Ctx? α := []

@[match_pattern]
def Ctx?.cons (Γ : Ctx? α) (v : Var? α) : Ctx? α := List.cons v Γ

def Ctx?.erase (Γ : Ctx? α) : Ctx? α := Γ.map Var?.erase

@[simp]
theorem Ctx?.erase_nil : Ctx?.erase (.nil : Ctx? α) = .nil := rfl

@[simp]
theorem Ctx?.erase_cons (Γ : Ctx? α) (v : Var? α)
  : Ctx?.erase (Ctx?.cons Γ v) = Ctx?.cons (Ctx?.erase Γ) v.erase := rfl

@[match_pattern]
abbrev Ctx?.cons' (Γ : Ctx? α) (A : Ty α) (q : EQuant) : Ctx? α
  := Γ.cons ⟨A, q⟩

@[elab_as_elim, cases_eliminator]
def Ctx?.casesOn {motive : Ctx? α → Sort _} (Γ : Ctx? α)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive (.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v

@[elab_as_elim, induction_eliminator]
def Ctx?.inductionOn {motive : Ctx? α → Sort _} (Γ : Ctx? α)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive Γ → motive (Ctx?.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v (inductionOn Γ nil cons)

@[simp]
theorem Ctx?.erase_erase (Γ : Ctx? α) : Ctx?.erase (Ctx?.erase Γ) = Ctx?.erase Γ := by
  induction Γ <;> simp [*]

def Ctx?.length (Γ : Ctx? α) : ℕ := List.length Γ

@[simp]
theorem Ctx?.length_nil : Ctx?.length (.nil : Ctx? α) = 0 := rfl

@[simp]
theorem Ctx?.length_cons (Γ : Ctx? α) (v : Var? α)
  : Ctx?.length (Ctx?.cons Γ v) = Ctx?.length Γ + 1 := rfl

theorem Ctx?.length_cons' (Γ : Ctx? α) (A : Ty α) (q : EQuant)
  : Ctx?.length (Ctx?.cons' Γ A q) = Ctx?.length Γ + 1 := rfl

@[simp]
def Ctx?.ety : Ctx? α → Ty α
  | .nil => Ty.unit
  | .cons Γ v => .tensor (Ctx?.ety Γ) v.ety

@[ext]
theorem Var?.ext {v w : Var? α}
  (h : v.ty = w.ty) (h' : v.q = w.q) : v = w :=
  by cases v; cases w; cases h; cases h'; rfl

abbrev Var?.unused (v : Var? α) : Prop := v.q = 0

@[simp]
theorem Var?.unused.eq_erase {v : Var? α} (h : v.unused) : v.erase = v
  := by cases v; cases h; rfl

abbrev Var?.used (v : Var? α) : Prop := 1 ≤ v.q

theorem Var?.used_iff {v : Var? α} : v.used ↔ ¬v.unused := EQuant.one_le_iff_ne_zero _

theorem Var?.unused_iff {v : Var? α} : v.unused ↔ ¬v.used := by simp [used_iff]

variable [HasQuant α]

open HasQuant

instance Var?.hasQuant : HasQuant (Var? α) where
  quant v := match v.q with | 0 => ⊤ | (q : Quant) => q ⊓ quant v.ty

instance Ctx?.hasQuant : HasQuant (Ctx? α) where
  quant Γ := Γ.foldr (λv q => q ⊓ quant v) ⊤

@[simp] theorem Ctx?.quant_nil : quant (.nil : Ctx? α) = ⊤ := rfl

@[simp]
theorem Ctx?.quant_cons (Γ : Ctx? α) (v : Var? α)
  : quant (Ctx?.cons Γ v) = quant Γ ⊓ quant v := rfl

@[simp]
theorem Var?.quant_erase (v : Var? α) : quant (Var?.erase v) = ⊤ := rfl

@[simp]
theorem Ctx?.quant_erase (Γ : Ctx? α) : quant (Ctx?.erase Γ) = ⊤ := by induction Γ <;> simp [*]

abbrev Var?.del (v : Var? α) : Prop := IsAff v

abbrev Var?.copy (v : Var? α) : Prop := IsRel v

@[simp]
instance Var?.del.instZeroQuant (A : Ty α) : (⟨A, 0⟩ : Var? α).del
  := ⟨by simp [quant]⟩

@[simp]
instance Var?.copy.instZeroQuant (A : Ty α) : (⟨A, 0⟩ : Var? α).copy
  := ⟨by simp [quant]⟩

@[simp]
instance Var?.del.instErase (v : Var? α) : v.erase.del := ⟨by simp⟩

@[simp]
instance Var?.copy.instErase (v : Var? α) : v.erase.copy := ⟨by simp⟩

theorem Var?.del.q (v : Var? α) [hv : v.del] : 0 ≤ v.q := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => simp
  | rest => simp only [IsAff.is_aff_iff, quant, le_inf_iff] at hv; exact hv.1

theorem Var?.del.ty (v : Var? α) [hv : v.del] (h : v.used) : IsAff v.ty := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => simp at h
  | rest => simp only [IsAff.is_aff_iff, quant, le_inf_iff] at *; exact hv.2

theorem Var?.del_iff (v : Var? α) : v.del ↔ 0 ≤ v.q ∧ (v.used -> IsAff v.ty) := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => simp [quant, IsAff.is_aff_iff]
  | rest q => simp [quant, IsAff.is_aff_iff, quant]; intro _; cases q <;> decide

structure Var?.scopy (v : Var? α) : Prop where
  q : EQuant.copy ≤ v.q
  ty : IsRel v.ty

theorem Var?.scopy_iff (v : Var? α) : v.scopy ↔ (EQuant.copy ≤ v.q ∧ IsRel v.ty)
  := ⟨λh => ⟨h.1, h.2⟩, λh => ⟨h.1, h.2⟩⟩

theorem Var?.used.scopy {v : Var? α} (h : v.used) [hv : v.copy] : v.scopy := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => simp at h
  | rest => simp only [IsRel.is_rel_iff, quant, le_inf_iff] at hv; exact ⟨hv.1, ⟨hv.2⟩⟩

theorem Var?.unused.del {v : Var? α} (h : v.unused) : v.del
  := by simp only [unused] at h; simp [IsAff.is_aff_iff, quant, h]

theorem Var?.unused.copy {v : Var? α} (h : v.unused) : v.copy
  := by simp only [unused] at h; simp [IsRel.is_rel_iff, quant, h]

@[simp]
theorem Var?.unused.quant_top {v : Var? α} (h : v.unused) : quant v = ⊤ := by simp [quant, h]

theorem Var?.scopy.copy {v : Var? α} (h : v.scopy) : v.copy := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => simp [IsRel.is_rel_iff, quant]
  | rest => simp [IsRel.is_rel_iff, quant]; constructor; exact h.q; exact h.ty.copy_le_quant

theorem Var?.copy_iff (v : Var? α) : v.copy ↔ (v.used -> v.scopy)
  := ⟨λ_ u => u.scopy, λh => if u : v.unused then u.copy else (h (used_iff.mpr u)).copy⟩

instance Var?.del.instTopQuant (A : Ty α) [IsAff A] : (⟨A, ⊤⟩ : Var? α).del
  := by simp [del_iff, *]

instance Var?.copy.instTopQuant (A : Ty α) [IsRel A] : (⟨A, ⊤⟩ : Var? α).copy
  := by simp [copy_iff, scopy_iff, *]

instance Var?.del.instDelQuant (A : Ty α) [IsAff A] : (⟨A, .del⟩ : Var? α).del
  := by simp [del_iff, *]

instance Var?.copy.instCopyQuant (A : Ty α) [IsRel A] : (⟨A, .copy⟩ : Var? α).copy
  := by simp [copy_iff, scopy_iff, *]

theorem Ctx?.quant_le_of_quant_le_cons (Γ : Ctx? α) (h : q ≤ quant (Γ.cons v)) : q ≤ quant Γ
  := by simp at h; exact h.1

theorem Ctx?.quant_le_var_of_quant_le_cons (Γ : Ctx? α) (h : q ≤ quant (Γ.cons v)) : q ≤ quant v
  := by simp at h; exact h.2

instance Var?.copy.ety_rel (v : Var? α) [h : v.copy] : IsRel v.ety := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => simp only [ety]; infer_instance
  | rest => simp [quant, IsRel.is_rel_iff] at h; exact ⟨h.2⟩

instance Var?.del.ety_aff (v : Var? α) [h : v.del] : IsAff v.ety := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => simp only [ety]; infer_instance
  | rest => simp [quant, IsAff.is_aff_iff] at h; exact ⟨h.2⟩

abbrev Ctx?.copy (Γ : Ctx? α) : Prop := IsRel Γ

abbrev Ctx?.del (Γ : Ctx? α) : Prop := IsAff Γ

@[simp]
instance Ctx?.nil_copy : (.nil : Ctx? α).copy := ⟨by simp⟩

@[simp]
instance Ctx?.nil_del : (.nil : Ctx? α).del := ⟨by simp⟩

@[simp]
instance Ctx?.erase_copy (Γ : Ctx? α) : Γ.erase.copy := ⟨by induction Γ <;> simp [*]⟩

@[simp]
instance Ctx?.erase_del (Γ : Ctx? α) : Γ.erase.del := ⟨by induction Γ <;> simp [*]⟩

@[simp]
theorem Ctx?.cons_copy_iff (Γ : Ctx? α) (v : Var? α) : (Γ.cons v).copy ↔ Γ.copy ∧ v.copy
  := ⟨λ⟨h⟩ => by simp at h; exact ⟨⟨h.1⟩, ⟨h.2⟩⟩, λ⟨⟨hΓ⟩, ⟨hv⟩⟩ => ⟨by simp [*]⟩⟩

@[simp]
theorem Ctx?.copy.tail (Γ : Ctx? α) (v : Var? α) [h : (Γ.cons v).copy] : Γ.copy
  := by rw [cons_copy_iff] at h; exact h.1

@[simp]
theorem Ctx?.copy.head (Γ : Ctx? α) (v : Var? α) [h : (Γ.cons v).copy] : v.copy
  := by rw [cons_copy_iff] at h; exact h.2

@[simp]
instance Ctx?.copy.cons (Γ : Ctx? α) (v : Var? α) [Γ.copy] [v.copy] : (Γ.cons v).copy
  := ⟨by simp [cons_copy_iff, *]⟩

@[simp]
theorem Ctx?.cons_del_iff (Γ : Ctx? α) (v : Var? α) : (Γ.cons v).del ↔ Γ.del ∧ v.del
  := ⟨λ⟨h⟩ => by simp at h; exact ⟨⟨h.1⟩, ⟨h.2⟩⟩, λ⟨⟨hΓ⟩, ⟨hv⟩⟩ => ⟨by simp [*]⟩⟩

@[simp]
theorem Ctx?.del.tail (Γ : Ctx? α) (v : Var? α) [h : (Γ.cons v).del] : Γ.del
  := by rw [cons_del_iff] at h; exact h.1

@[simp]
theorem Ctx?.del.head (Γ : Ctx? α) (v : Var? α) [h : (Γ.cons v).del] : v.del
  := by rw [cons_del_iff] at h; exact h.2

@[simp]
instance Ctx?.del.cons (Γ : Ctx? α) (v : Var? α) [Γ.del] [v.del] : (Γ.cons v).del
  := ⟨by simp [cons_del_iff, *]⟩

@[simp]
instance Ctx?.ety_rel_of_copy {Γ : Ctx? α} [h : Γ.copy] : IsRel (Ctx?.ety Γ) := by
  generalize h = h
  induction Γ with
  | nil => constructor; simp [ety]
  | cons Γ v I =>
    have _ := I (copy.tail Γ v)
    have _ := copy.head Γ v
    simp only [ety]
    apply IsRel.tensor

@[simp]
instance Ctx?.ety_aff_of_del {Γ : Ctx? α} [h : Γ.del] : IsAff (Ctx?.ety Γ) := by
  generalize h = h
  induction Γ with
  | nil => constructor; simp [ety]
  | cons Γ v I =>
    have _ := I (del.tail Γ v)
    have _ := del.head Γ v
    simp only [ety]
    apply IsAff.tensor

structure Var?.Wk (v w : Var? α) : Prop where
  ty : v.ty = w.ty
  q : w.q ≤ v.q
  unused_del : w.unused → v.del

instance Var?.instLE : LE (Var? α) := ⟨Wk⟩

theorem Var?.erase_mono {v w : Var? α} (h : v ≤ w) : v.erase ≤ w.erase := by
  cases v with | mk A q => cases w with | mk A' q' =>
    exact ⟨h.ty, le_refl _, λ_ => inferInstance⟩

theorem Var?.used.anti {v w : Var? α} (h : v ≤ w) (hw : w.used) : v.used := hw.trans h.q

theorem Var?.unused.mono {v w : Var? α} (h : v ≤ w) : (hv : v.unused) → w.unused
  := by simp only [unused_iff, not_imp_not]; exact used.anti h

theorem Var?.del.anti {v w : Var? α} (h : v ≤ w) [hw : w.del] : v.del := open Classical in
  if hw' : w.used then
    by rw [del_iff] at *; exact ⟨hw.1.trans h.q, λ_ => h.ty ▸ hw.2 hw'⟩
  else
    h.unused_del (unused_iff.mpr hw')

theorem Var?.del.wk {v w : Var? α} (ρ : v ≤ w) (hw : w.del) : v.del := hw.anti ρ

theorem Var?.scopy.anti {v w : Var? α} (h : v ≤ w) (hw : w.scopy) : v.scopy where
  q := hw.q.trans h.q
  ty := h.ty ▸ hw.ty

theorem Var?.used.scopy_anti {v w : Var? α} (h : v ≤ w) (hw' : w.used) [hw : w.copy] : v.scopy
  := by rw [copy_iff] at *; exact (hw hw').anti h

theorem Var?.copy.anti {v w : Var? α} (h : v ≤ w) [hw : w.copy] (hw' : w.used) : v.copy
  := (hw'.scopy_anti h).copy

theorem Var?.used.quant_anti {v w : Var? α} (h : v ≤ w) (hw : w.used) : quant w ≤ quant v := by
  cases w with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases hw
    | rest => cases v; cases h.ty; cases h.q using EQuant.le.casesLE <;> simp [quant]

instance Var?.instPartialOrder : PartialOrder (Var? α) where
  le_refl _ := ⟨rfl, le_refl _, λh => h.del⟩
  le_trans _ _ _ h h' :=
    ⟨h.ty.trans h'.ty, h'.q.trans h.q, λx => (x.del.anti h').anti h⟩
  le_antisymm _ _ h h' := ext h.ty (le_antisymm h'.q h.q)

theorem Var?.Wk.ety_aff {v w : Var? α} (h : v.Wk w) (hv : IsAff v.ety) : IsAff w.ety
  := by cases w using Var?.casesZero with
  | zero A => infer_instance
  | rest A q => cases v using Var?.casesZero with
    | zero A => cases h.ty; cases h.q using EQuant.le.casesLE
    | rest A q => cases h.ty; exact hv

theorem Var?.Wk.ety_aff' {v w : Var? α} (h : v.Wk w) (hv : IsAff w.ety) : IsAff v.ety
  := by cases v using Var?.casesZero with
  | zero A => infer_instance
  | rest A q => cases w using Var?.casesZero with
    | zero A => exact ⟨le_trans (h.unused_del (by simp)).del_le_quant (by simp [quant, ety])⟩
    | rest A q => cases h.ty; exact hv

theorem Var?.Wk.ety_aff_zero {B : Ty α} (h : v ≤ Var?.mk B 0)
  : IsAff v.ety := del.ety_aff _ (h := del.anti h)

theorem Var?.Wk.ety_eq_quant {B : Ty α} {q : Quant} (h : v ≤ Var?.mk B q)
  : v.ety = B := by
  cases v with | mk A q' => cases q' using EQuant.casesZero with
  | zero => cases h.q using EQuant.le.casesLE
  | rest => cases h.ty; rfl

theorem Var?.Wk.ety_eq_used {v w : Var? α} (h : v ≤ w) (hw : w.used) : v.ety = w.ety := by
  cases w with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases hw
    | rest => rw [ety_eq_quant h]

theorem Var?.del.erase_le (v : Var? α) [hv : v.del] : v ≤ v.erase := ⟨
  rfl,
  by cases v with | mk A q => cases q using EQuant.casesZero with | zero => rfl | rest q =>
    simp [IsAff.is_aff_iff', quant] at *; apply le_trans hv; simp,
  λ_ => hv
⟩

theorem Var?.del.of_erase_le {v : Var? α} (h : v ≤ v.erase) : v.del := by
  cases v with | mk A q => cases q using EQuant.casesZero with
  | zero => infer_instance
  | rest q => exact h.unused_del (by simp)

theorem Var?.del_iff_erase_le {v : Var? α} : v.del ↔ v ≤ v.erase
  := ⟨λ_ => del.erase_le v, del.of_erase_le⟩

theorem Var?.Wk.quant_le_quant_iff  {A B : Ty α} {q q' : Quant}
  : Var?.mk A q ≤ Var?.mk B q' ↔ A = B ∧ q' ≤ q :=
  ⟨λh => ⟨h.ty, h.q⟩, λ⟨ht, hq⟩ => ⟨ht, hq, (by simp)⟩⟩

theorem Var?.Wk.not_zero_le {A B : Ty α} {q : Quant}  (h : Var?.mk A 0 ≤ ⟨B, q⟩) : False
  := by cases h.q using EQuant.le.casesLE

@[simp]
theorem Var?.Wk.zero_le_quant_iff {A B : Ty α} {q : Quant} : (Var?.mk A 0 ≤ ⟨B, q⟩) ↔ False
  := by rw [iff_false]; apply not_zero_le

@[simp]
theorem Var?.Wk.le_quant_iff  {A B : Ty α} {q : EQuant} {q' : Quant}
  : Var?.mk A q ≤ Var?.mk B q' ↔ A = B ∧ q' ≤ q := by cases q using EQuant.casesZero with
  | zero => simp only [zero_le_quant_iff, false_iff, not_and]; intro h; cases q' <;> decide
  | rest => simp [quant_le_quant_iff]

@[simp]
theorem Var?.Wk.zero_le_zero_iff {A B : Ty α} : Var?.mk A 0 ≤ Var?.mk B 0 ↔ A = B
  := ⟨λh => h.ty, λh => ⟨h, le_refl _, by simp⟩⟩

theorem Var?.Wk.zero_le_iff {A} {v : Var? α} : ⟨A, 0⟩ ≤ v ↔ A = v.ty ∧ v.unused
  := by cases v with | mk B q => cases q using EQuant.casesZero <;> simp

theorem Var?.Wk.zero_le_unused {A} {v : Var? α} (h : ⟨A, 0⟩ ≤ v) : v.unused
  := by cases v with | mk B q => cases q using EQuant.casesZero with
  | zero => rfl
  | rest q => exact h.not_zero_le.elim

theorem Var?.Wk.erase_eq {v w : Var? α} (h : v.Wk w) : v.erase = w.erase
  := by cases v; cases w; cases h.ty; rfl

inductive Ctx?.PWk : Ctx? α → Ctx? α → Type _ where
  | nil : Ctx?.PWk .nil .nil
  | cons {Γ Δ v w} (h : Ctx?.PWk Γ Δ) (hvw : v ≤ w) : Ctx?.PWk (Ctx?.cons Γ v) (Ctx?.cons Δ w)

abbrev Ctx?.PWk.scons {Γ Δ : Ctx? α} (v : Var? α) (ρ : Γ.PWk Δ)
  := ρ.cons (le_refl v)

theorem Ctx?.PWk.head {Γ Δ v w} (h : PWk (α := α) (.cons Γ v) (.cons Δ w)) : v ≤ w
  := match h with | Ctx?.PWk.cons _ hvw => hvw

def Ctx?.PWk.tail {Γ Δ v w} (h : PWk (α := α) (.cons Γ v) (.cons Δ w)) : PWk Γ Δ
  := match h with | Ctx?.PWk.cons h _ => h

@[simp]
def Ctx?.PWk.refl : (Γ : Ctx? α) → PWk Γ Γ
  | .nil => .nil
  | .cons Γ v => .cons (refl Γ) (le_refl v)

@[simp]
def Ctx?.PWk.comp {Γ Δ Ξ : Ctx? α} : (ρ : PWk Γ Δ) → (ρ' : PWk Δ Ξ) → PWk Γ Ξ
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (h.comp h') (le_trans hvw hvw')

instance Ctx?.PWk.instSubsingleton {Γ Δ : Ctx? α} : Subsingleton (PWk Γ Δ) where
  allEq ρ ρ' := by induction ρ <;> cases ρ' <;> simp; apply_assumption

theorem Ctx?.PWk.antisymm {Γ Δ : Ctx? α} (h : PWk Γ Δ) (h' : PWk Δ Γ) : Γ = Δ := by
  induction h with
  | nil => rfl
  | cons h hvw I => cases h' with
  | cons h' hwv => rw [I h', le_antisymm hvw hwv]

theorem Ctx?.PWk.length {Γ Δ : Ctx? α} (h : PWk Γ Δ) : Ctx?.length Γ = Ctx?.length Δ
  := by induction h <;> simp [*]

inductive Ctx?.Wk : Ctx? α → Ctx? α → Type _ where
  | nil : Ctx?.Wk .nil .nil
  | cons {Γ Δ v w} (h : Ctx?.Wk Γ Δ) (hvw : v ≤ w) : Ctx?.Wk (Ctx?.cons Γ v) (Ctx?.cons Δ w)
  | skip {Γ Δ v} (h : Ctx?.Wk Γ Δ) (hv : v.del) : Ctx?.Wk (Ctx?.cons Γ v) Δ

@[match_pattern]
abbrev Ctx?.Wk.scons {Γ Δ : Ctx? α} (v : Var? α) (ρ : Γ.Wk Δ)
  := ρ.cons (le_refl v)

theorem Ctx?.Wk.length {Γ Δ : Ctx? α} (h : Wk Γ Δ) : Ctx?.length Δ ≤ Ctx?.length Γ
  := by induction h <;> simp <;> omega

@[simp]
def Ctx?.PWk.toWk {Γ Δ : Ctx? α} : PWk Γ Δ → Wk Γ Δ
  | .nil => .nil
  | .cons h hvw => .cons (toWk h) hvw

instance Ctx?.PWk.coeWk {Γ Δ : Ctx? α} : Coe (PWk Γ Δ) (Wk Γ Δ) := ⟨toWk⟩

@[simp]
def Ctx?.Wk.toPWk {Γ Δ : Ctx? α} (h : Γ.length = Δ.length) : (ρ : Wk Γ Δ) → Γ.PWk Δ
  | .nil => .nil
  | .skip ρ hw => by have _ := ρ.length; simp at h; omega
  | .cons ρ hw => .cons (ρ.toPWk (by convert h using 0; simp)) hw

@[simp]
theorem Ctx?.Wk.toWk_toPWk {Γ Δ : Ctx? α} (h : Γ.length = Δ.length) (ρ : Wk Γ Δ)
  : (ρ.toPWk h).toWk = ρ := by induction ρ with
  | skip ρ => have _ := ρ.length; simp at h; omega
  | _ => simp [*]

theorem Ctx?.Wk.antisymm {Γ Δ : Ctx? α} (h : Wk Γ Δ) (h' : Wk Δ Γ) : Γ = Δ :=
  have hl := le_antisymm h'.length h.length
  PWk.antisymm (h.toPWk hl) (h'.toPWk (hl.symm))

-- toPWk is a faithful functor
theorem Ctx?.Wk.eq_pwk {Γ Δ : Ctx? α} (ρ : Wk Γ Δ) (h : Γ.length = Δ.length)
  : (ρ.toPWk h).toWk = ρ := by induction ρ with
  | nil => rfl
  | cons ρ v I => simp [I (by convert h using 0; simp)]
  | skip ρ =>
    have hl := ρ.length
    rw [<-h, length_cons] at hl
    omega

theorem Ctx?.Wk.eq_of_length_eq {Γ Δ : Ctx? α} (ρ ρ' : Wk Γ Δ) (h : Γ.length = Δ.length)
  : ρ = ρ' := by rw [<-eq_pwk ρ h, <-eq_pwk ρ' h]; congr 1; apply Subsingleton.elim

theorem Ctx?.Wk.subsingleton_of_length_eq (Γ Δ : Ctx? α) (h : Γ.length = Δ.length)
  : Subsingleton (Wk Γ Δ) := ⟨λ_ _ => eq_of_length_eq _ _ h⟩

@[simp]
def Ctx?.Wk.refl : (Γ : Ctx? α) → Wk Γ Γ
  | .nil => .nil
  | .cons Γ v => .cons (refl Γ) (le_refl v)

theorem Ctx?.Wk.eq_refl {Γ : Ctx? α} (h : Wk Γ Γ) : h = Wk.refl Γ := eq_of_length_eq _ _ rfl

def Ctx?.Wk.ofEq {Γ Δ : Ctx? α} (h : Γ = Δ) : Wk Γ Δ := h ▸ (refl Γ)

@[simp]
theorem Ctx?.Wk.ofEq_refl {Γ : Ctx? α} : Ctx?.Wk.ofEq (Eq.refl Γ) = Wk.refl Γ := rfl

def Ctx?.PWk.ofEq {Γ Δ : Ctx? α} (h : Γ = Δ) : PWk Γ Δ := h ▸ (refl Γ)

@[simp]
theorem Ctx?.PWk.ofEq_refl {Γ : Ctx? α} : Ctx?.PWk.ofEq (Eq.refl Γ) = PWk.refl Γ := rfl

theorem Ctx?.Wk.ofEq_cons {Γ Δ : Ctx? α} (h : Γ.cons v = Δ.cons w)
  : Wk.ofEq h = (Wk.ofEq (by cases h; rfl)).cons (le_of_eq (by cases h; rfl)) := by cases h; rfl

theorem Ctx?.PWk.ofEq_cons {Γ Δ : Ctx? α} (h : Γ.cons v = Δ.cons w)
  : PWk.ofEq h = (PWk.ofEq (by cases h; rfl)).cons (le_of_eq (by cases h; rfl)) := by cases h; rfl

@[simp]
theorem Ctx?.PWk.toWk_refl {Γ : Ctx? α} : (PWk.refl Γ).toWk = Wk.refl Γ := by
  induction Γ <;> simp [*]

@[simp]
theorem Ctx?.PWk.toWk_ofEq {Γ Δ : Ctx? α} (h : Γ = Δ) : (PWk.ofEq h).toWk = Wk.ofEq h := by
  cases h; simp

def Ctx?.wk0 (Γ : Ctx? α) (v : Var? α) [hv : v.del] : Wk (Γ.cons v) Γ := (Wk.refl Γ).skip hv

@[simp]
def Ctx?.Wk.comp {Γ Δ Ξ : Ctx? α} : Wk Γ Δ → Wk Δ Ξ → Wk Γ Ξ
  | .nil, .nil => .nil
  | .cons h hv, .cons h' hv' => .cons (h.comp h') (hv.trans hv')
  | .cons h hv, .skip h' hv' => .skip (h.comp h') (Var?.del.anti hv)
  | .skip h hv, h' => .skip (h.comp h') hv

@[simp]
theorem Ctx?.Wk.refl_comp {Γ Δ : Ctx? α} (ρ : Wk Γ Δ) : (Wk.refl Γ).comp ρ = ρ
  := by induction ρ <;> simp [*]

@[simp]
theorem Ctx?.Wk.comp_refl {Γ Δ : Ctx? α} (ρ : Wk Γ Δ) : ρ.comp (Wk.refl Δ) = ρ
  := by induction ρ <;> simp [*]

@[simp]
theorem Ctx?.Wk.comp_ofEq {Γ Δ Ξ : Ctx? α} (h : Γ = Δ) (h' : Δ = Ξ)
  : (Wk.ofEq h).comp (Wk.ofEq h') = Wk.ofEq (h.trans h')
  := by cases h; cases h'; simp

theorem Ctx?.Wk.comp_assoc {Γ Δ Ξ Θ : Ctx? α} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (h'' : Wk Ξ Θ)
  : h.comp (h'.comp h'') = (h.comp h').comp h'' := by induction h generalizing Ξ Θ with
  | nil => cases h'; cases h''; rfl
  | cons _ _ I => cases h' <;> cases h'' <;> simp [comp, I]
  | skip _ _ I => simp [comp, I]

theorem Ctx?.PWk.comp_toWk {Γ Δ Ξ : Ctx? α} (ρ : PWk Γ Δ) (ρ' : PWk Δ Ξ)
  : (ρ.comp ρ').toWk = ρ.toWk.comp ρ'.toWk
  := by induction ρ generalizing Ξ <;> cases ρ' <;> simp [*]

@[simp]
theorem Ctx?.PWk.refl_comp {Γ Δ : Ctx? α} (ρ : PWk Γ Δ) : (PWk.refl Γ).comp ρ = ρ
  := by induction ρ <;> simp [*]

@[simp]
theorem Ctx?.PWk.comp_refl {Γ Δ : Ctx? α} (ρ : PWk Γ Δ) : ρ.comp (PWk.refl Δ) = ρ
  := by induction ρ <;> simp [*]

@[simp]
theorem Ctx?.PWk.comp_ofEq {Γ Δ Ξ : Ctx? α} (h : Γ = Δ) (h' : Δ = Ξ)
  : (PWk.ofEq h).comp (PWk.ofEq h') = PWk.ofEq (h.trans h')
  := by cases h; cases h'; simp

theorem Ctx?.PWk.comp_assoc {Γ Δ Ξ Θ : Ctx? α} (h : PWk Γ Δ) (h' : PWk Δ Ξ) (h'' : PWk Ξ Θ)
  : h.comp (h'.comp h'') = (h.comp h').comp h'' := by induction h generalizing Ξ Θ with
  | nil => cases h'; cases h''; rfl
  | cons _ _ I => cases h'; cases h''; simp [comp, I]

@[simp]
def Ctx?.Wk.ix {Γ Δ : Ctx? α} : Wk Γ Δ → ℕ → ℕ
  | .nil => id
  | .cons h _ => Nat.liftWk h.ix
  | .skip h _ => Nat.stepWk h.ix

instance Ctx?.Wk.coeFunRen {Γ Δ : Ctx? α} : CoeFun (Wk Γ Δ) (λ_ => ℕ → ℕ) := ⟨ix⟩

@[simp]
theorem Ctx?.Wk.ix_increasing {Γ Δ : Ctx? α} (h : Wk Γ Δ) (i : ℕ) : i ≤ h i := by
  induction h generalizing i with
  | nil => simp [ix]
  | cons _ _ I => cases i <;> simp [ix, *]
  | skip _ _ I => simp [ix]; have I := I i; omega

@[simp]
theorem Ctx?.Wk.ix_comp_applied {Γ Δ Ξ : Ctx? α} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (i : ℕ)
  : (h.comp h') i = h (h' i) := by induction h generalizing Ξ i with
  | nil => cases h'; rfl
  | cons _ _ I => cases h' <;> cases i <;> simp [comp, ix, I]
  | skip _ _ I => simp [comp, ix, I]

theorem Ctx?.Wk.ix_comp {Γ Δ Ξ : Ctx? α} (h : Wk Γ Δ) (h' : Wk Δ Ξ)
  : (h.comp h').ix = h.ix ∘ h'.ix := funext (λi => Wk.ix_comp_applied h h' i)

theorem Ctx?.Wk.ix_length_eq_applied {Γ Δ : Ctx? α}
  (h : Γ.Wk Δ) (hl : Γ.length = Δ.length) (i : ℕ) : h i = i := by induction h generalizing i with
  | nil => rfl
  | cons _ _ I =>
    cases i; rfl; simp only [ix, Nat.liftWk_succ, add_left_inj]; apply I; convert hl using 0; simp
  | skip h _ => have hl' := h.length; rw [<-hl] at hl'; simp at hl'

theorem Ctx?.Wk.ix_length_eq {Γ Δ : Ctx? α} (h : Γ.Wk Δ) (hl : Γ.length = Δ.length)
  : h.ix = id := funext (λi => ix_length_eq_applied h hl i)

@[simp]
theorem Ctx?.Wk.ix_refl {Γ : Ctx? α} (h : Γ.Wk Γ) : h.ix = id := ix_length_eq _ rfl

@[simp]
theorem Ctx?.Wk.ix_ofEq {Γ Δ : Ctx? α} (h : Γ = Δ) : (Wk.ofEq h).ix = id
  := ix_length_eq _ (by cases h; rfl)

@[simp]
theorem Ctx?.Wk.ix_pwk {Γ Δ : Ctx? α} (h : Γ.PWk Δ) : h.toWk.ix = id := ix_length_eq _ h.length

-- TODO: ix is an injection...

theorem Ctx?.Wk.ix_bounded {Γ Δ : Ctx? α} (h : Γ.Wk Δ) (i : ℕ)
  (hi : i < Δ.length) : h.ix i < Γ.length
  := by induction h generalizing i with
  | nil => simp at hi
  | cons _ _ I =>
    cases i
    · simp [ix]
    · simp only [ix, Nat.liftWk_succ, length_cons, add_lt_add_iff_right]
      apply I; convert hi using 0; simp
  | skip _ _ I => simp [ix, *]

def Ctx?.Wk.skips {Γ Δ : Ctx? α} (h : Wk Γ Δ) : ℕ := h 0

--TODO: minimize and report because this is a _sin_
def Ctx?.drop (Γ : Ctx? α) [h : Γ.del] : Wk Γ .nil := (λh => match Γ with
  | .nil => .nil
  | .cons Γ _ => have _ := h.tail; .skip Γ.drop h.head) h

@[simp]
theorem Ctx?.Wk.drop_nil : (.nil : Ctx? α).drop = .nil := rfl

@[simp]
theorem Ctx?.Wk.drop_cons (Γ : Ctx? α) [hΓ : Γ.del] (v : Var? α) [hv : v.del]
  : (Ctx?.cons Γ v).drop = Γ.drop.skip inferInstance := rfl

theorem Ctx?.Wk.drop_del {Γ : Ctx? α} (w : Γ.Wk .nil) : Γ.del := by
  induction Γ <;> cases w <;> simp; constructor <;> apply_assumption; assumption

theorem Ctx?.wk_nil_eq_drop {Γ : Ctx? α} (w : Γ.Wk .nil) : w = Γ.drop (h := w.drop_del) := by
  induction Γ <;> cases w <;> rw [drop]; simp; apply_assumption

theorem Ctx?.wk_nil_unique {Γ : Ctx? α} (w w' : Γ.Wk .nil) : w = w' := by
  rw [wk_nil_eq_drop w, wk_nil_eq_drop w']

theorem Ctx?.del.wk {Γ Δ : Ctx? α} (h : Γ.Wk Δ) [hΔ : Δ.del] : Γ.del := (λhΔ => by
  induction h with
  | nil => infer_instance
  | cons Γ hvw I =>
    have _ := I hΔ.tail
    have _ := hΔ.head
    have hv := Var?.del.anti hvw
    infer_instance
  | skip _ _ I =>
    have _ := I hΔ
    infer_instance
  ) hΔ

@[simp]
def Ctx?.erasePWk (Γ : Ctx? α) [h : Γ.del] : PWk Γ Γ.erase := match Γ, h with
  | .nil, _ => .nil
  | .cons Γ _, h => .cons (Γ.erasePWk (h := h.tail)) (Var?.del_iff_erase_le.mp h.head)

@[simp]
def Ctx?.eraseWk (Γ : Ctx? α) [h : Γ.del] : Wk Γ Γ.erase := match Γ, h with
  | .nil, _ => .nil
  | .cons Γ _, h => .cons (Γ.eraseWk (h := h.tail)) (Var?.del_iff_erase_le.mp h.head)

theorem Ctx?.toWk_erasePWk {Γ : Ctx? α}
  : [h : Γ.del] → (Γ.erasePWk (h := h)).toWk = Γ.eraseWk (h := h)
  := by induction Γ <;> simp [*]

def Ctx?.choose_drop (Γ : Ctx? α) (h : Nonempty (Γ.Wk .nil)) : Γ.Wk .nil :=
  have _ : Γ.del := let ⟨h⟩ := h; h.drop_del; Γ.drop

def Var?.Ix (Γ : Ctx? α) (v : Var? α) : Type _ := Γ.Wk [v]

@[match_pattern]
def Var?.zero_le {Γ : Ctx? α} (x : Γ.Wk .nil) {v w : Var? α} (h : v ≤ w) : Ix (Γ.cons v) w
  := x.cons h

@[match_pattern]
abbrev Var?.zero {Γ : Ctx? α} (x : Γ.Wk .nil) (v : Var? α) : Ix (Γ.cons v) v
  := zero_le x (le_refl v)

@[match_pattern]
def Var?.Ix.succ {Γ : Ctx? α} (v : Var? α) [h : v.del] {w} (x : Ix Γ w) : Ix (Γ.cons v) w
  := x.skip h

@[elab_as_elim, cases_eliminator]
def Var?.Ix.casesOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx? α} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} (v : Var? α) (_ : v.del) {w} (x : Ix Γ w), motive (succ v x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ _ _ x

@[elab_as_elim, induction_eliminator]
def Var?.Ix.inductionOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx? α} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} {v : Var? α} (h : v.del) {w} (x : Ix Γ w), motive x → motive (succ v (h := h) x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ hv x (inductionOn x zero_le succ)

def Var?.Ix.ix {Γ : Ctx? α} {v} (x : Ix Γ v) : ℕ := x.skips

@[simp]
theorem Var?.ix_zero_le {Γ : Ctx? α} {v w : Var? α} (h : v ≤ w) (x : Γ.Wk .nil)
  : (zero_le x h).ix = 0 := rfl

@[simp]
theorem Var?.Ix.ix_succ {Γ : Ctx? α} (v : Var? α) [h : v.del] {w} (x : Ix Γ w)
  : (succ v x).ix = x.ix + 1 := rfl

def Var?.Ix.wk {Γ Δ : Ctx? α} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : Ix Γ v := h.comp x

theorem Var?.Ix.wk_wk {Γ Δ Ξ : Ctx? α} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : (x.wk h').wk h = x.wk (h.comp h') := Ctx?.Wk.comp_assoc h h' x

theorem Var?.Ix.wk_comp {Γ Δ Ξ : Ctx? α} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : x.wk (h.comp h') = (x.wk h').wk h := (x.wk_wk h h').symm

@[simp]
theorem Var?.Ix.succ_wk_cons {Γ Δ : Ctx? α} (h : Γ.Wk Δ)
  {v v' : Var? α} (hv : v ≤ v') [hv' : IsAff v'] {w} (x : Ix Δ w)
  : (succ _ x).wk (h.cons hv) = (succ _ (h := del.anti hv) (x.wk h)) := rfl

@[simp]
theorem Var?.Ix.wk_skip {Γ Δ : Ctx? α} (h : Γ.Wk Δ)
  (v : Var? α) [hv : IsAff v] {w} (x : Ix Δ w)
  : x.wk (h.skip hv) = (x.wk h).succ v := rfl

@[simp]
theorem Var?.Ix.ix_wk {Γ Δ : Ctx? α} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : (x.wk h).ix = h.ix x.ix
  := by rw [ix, Ctx?.Wk.skips, wk, Ctx?.Wk.ix_comp]; rfl

theorem Var?.Ix.ix_wk_le {Γ Δ : Ctx? α} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : x.ix ≤ (x.wk h).ix
  := by simp

-- TODO: ix is an injection on variables...

inductive Ctx?.At (v : Var? α) : Ctx? α → ℕ → Type _ where
  | here {Γ} (d : Γ.del) {w} : w ≤ v → Ctx?.At v (Ctx?.cons Γ w) 0
  | there {Γ w n} (x : Ctx?.At v Γ n) (hw : w.del) : Ctx?.At v (Ctx?.cons Γ w) (n + 1)

instance Ctx?.At.instSubsingleton {v : Var? α} {Γ : Ctx? α} {n} : Subsingleton (Ctx?.At v Γ n) where
  allEq x y := by induction x <;> cases y <;> simp; apply_assumption

def Ctx?.At.cast {v v' : Var? α} {Γ Γ' : Ctx? α} {n n'}
  (x : Γ.At v n) (hΓ : Γ = Γ') (hv : v = v') (hn : n = n') : Γ'.At v' n'
  := hΓ ▸ hv ▸ hn ▸ x

@[simp]
theorem Ctx?.At.cast_rfl {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n) : x.cast rfl rfl rfl = x
  := rfl

@[simp]
theorem Ctx?.At.cast_cast {v v' v'' : Var? α} {Γ Γ' Γ'' : Ctx? α} {n n' n''}
  (x : Γ.At v n) (hΓ : Γ = Γ') (hv : v = v') (hn : n = n')
  (hΓ' : Γ' = Γ'') (hv' : v' = v'') (hn' : n' = n'')
  : (x.cast hΓ hv hn).cast hΓ' hv' hn' = x.cast (hΓ.trans hΓ') (hv.trans hv') (hn.trans hn')
  := by cases hΓ; cases hv; cases hn; cases hΓ'; cases hv'; cases hn'; rfl

@[simp]
theorem Ctx?.At.cast_here {v v' w : Var? α} {Γ Γ' : Ctx? α}
  (hΓ : Γ.cons w = Γ'.cons w) (hv : v = v')
  {d : Γ.del} (hw : w ≤ v)
  : (At.here d hw).cast hΓ hv rfl = .here (by cases hΓ; exact d) (hv ▸ hw)
  := by cases hΓ; cases hv; rfl

@[simp]
theorem Ctx?.At.cast_there {v v' w : Var? α} {Γ Γ' : Ctx? α} {n n'}
  (x : Γ.At v n) (hΓ : Γ.cons w = Γ'.cons w) (hv : v = v') (hn : n + 1 = n' + 1)
  {hw : w.del}
  : (x.there hw).cast hΓ hv hn = (x.cast (by cases hΓ; rfl) hv (by cases hn; rfl)).there hw
  := by cases hΓ; cases hv; cases hn; rfl

abbrev Ctx?.At.cast_src {v : Var? α} {Γ Γ' : Ctx? α} {n}
  (x : Γ.At v n) (hΓ : Γ = Γ') : Γ'.At v n
  := x.cast hΓ rfl rfl

abbrev Ctx?.At.cast_trg {v v' : Var? α} {Γ : Ctx? α} {n}
  (x : Γ.At v n) (hv : v = v') : Γ.At v' n
  := x.cast rfl hv rfl

abbrev Ctx?.At.cast_idx {v : Var? α} {Γ : Ctx? α} {n n'}
  (x : Γ.At v n) (hn : n = n') : Γ.At v n'
  := x.cast rfl rfl hn

theorem Ctx?.At.zero_cons_head {Γ : Ctx? α} {v} (h : (Γ.cons w).At v 0) : w ≤ v
  := by cases h; assumption

theorem Ctx?.At.zero_cons_tail {Γ : Ctx? α} {v} (h : (Γ.cons w).At v 0) : Γ.del
  := by cases h; assumption

theorem Ctx?.At.succ_cons_head {Γ : Ctx? α} {v w} (h : (Γ.cons w).At v (n + 1)) : w.del
  := by cases h; assumption

def Ctx?.At.succ_cons_tail {Γ : Ctx? α} {v w} (h : (Γ.cons w).At v (n + 1)) : Γ.At v n
  := by cases h; assumption

def Ctx?.At.pwk {v : Var? α} {Γ Δ : Ctx? α} : (ρ : Γ.PWk Δ) → ∀{n}, Δ.At v n → Γ.At v n
  | .cons ρ hvw, _, .here d hvw' => .here (d.wk ρ.toWk) (le_trans hvw hvw')
  | .cons ρ hvw, _, .there x hw => .there (x.pwk ρ) (hw.wk hvw)

def Ctx?.At.wkOut {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n) (hvw : v ≤ w)
  : Γ.At w n := match x with
  | .here d hw => .here d (le_trans hw hvw)
  | .there x hw => .there (x.wkOut hvw) hw

def Ctx?.At.wkIn {Γ Δ : Ctx? α} : (ρ : Γ.Wk Δ) → ∀{v : Var? α} {n}, Δ.At v n → Γ.At v (ρ n)
  | .cons ρ hvw, _, _, .here d hw => .here (d.wk ρ) (le_trans hvw hw)
  | .cons ρ hvw, _, _, .there a hw => .there (a.wkIn ρ) (hw.anti hvw)
  | .skip ρ hv, _, _, a => .there (a.wkIn ρ) hv

theorem Ctx?.At.ty_eq {Γ : Ctx? α} {v v'} {n} (x : Γ.At v n) (y : Γ.At v' n) : v.ty = v'.ty := by
  induction x with
  | here _ h => cases y with | here _ h' => rw [<-h.ty, <-h'.ty]
  | there => cases y; apply_assumption; assumption

theorem Ctx?.At.wkIn_toWk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {v : Var? α} {n} (x : Δ.At v n)
  : x.wkIn ρ.toWk = (x.pwk ρ).cast_idx (by simp) := by
  induction x generalizing Γ <;> cases ρ <;> simp [wkIn, pwk, *]

theorem Ctx?.At.wkIn_refl {Γ : Ctx? α} {v : Var? α} {n} (x : Γ.At v n)
  : x.wkIn (Wk.refl Γ) = x.cast_idx (by simp) := by induction x <;> simp [wkIn, *]

theorem Ctx?.At.wkIn_refl' {Γ : Ctx? α} (ρ : Γ.Wk Γ) {v : Var? α} {n} (x : Γ.At v n)
  : x.wkIn ρ = x.cast_idx (by simp)
  := by convert wkIn_refl x <;> apply Ctx?.Wk.eq_of_length_eq <;> rfl

theorem Ctx?.At.pwk_refl {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n)
  : x.pwk (PWk.refl Γ) = x := by induction x <;> simp [pwk, *]

@[simp]
theorem Ctx?.At.pwk_refl' {v : Var? α} {Γ : Ctx? α} {n} (x : Γ.At v n)
  : x.pwk (PWk.refl Γ) = x := by convert pwk_refl x

def Ctx?.At.ix {Γ : Ctx? α} {v n} : Γ.At v n → v.Ix Γ
  | .here _ hw => Var?.zero_le (Ctx?.drop _) hw
  | .there x hw => x.ix.succ _

@[simp]
theorem Ctx?.At.ix_ix {Γ : Ctx? α} {v n} (h : Γ.At v n) : h.ix.ix = n
  := by induction h <;> simp [ix, wkIn]; assumption

def Var?.Ix.at {Γ : Ctx? α} {v} : (x : Ix Γ v) → Γ.At v x.ix
  | .cons ρ hvw => .here ρ.drop_del hvw
  | .skip ρ hv => .there (Ix.at ρ) hv

-- TODO: so therefore at_ix is just the identity
