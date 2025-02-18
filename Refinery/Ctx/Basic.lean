import Refinery.Ty
import Discretion.Wk.Nat

namespace Refinery

universe u v

structure Var? (α : Type u) (ε : Type v) where
  ty : Ty α
  q : EQuant
  eff : ε

abbrev Var?.erase (v : Var? α ε) : Var? α ε := ⟨v.ty, 0, v.eff⟩

@[simp]
abbrev ety_var {α : Type u} (a : Ty α) : EQuant → Ty α
  | 0 => .unit
  | (q : Quant) => a

abbrev Var?.ety {α ε} (v : Var? α ε) : Ty α := ety_var v.ty v.q

theorem Var?.ety_quant_zero {A : Ty α} {e : ε} : Var?.ety ⟨A, 0, e⟩ = Ty.unit := rfl

theorem Var?.ety_quant_ty {A : Ty α} {q : Quant} {e : ε} : Var?.ety ⟨A, q, e⟩ = A := rfl

theorem Var?.ety_erase {v : Var? α ε} : v.erase.ety = Ty.unit := rfl

def Ctx? (α : Type u) (ε : Type v) := List (Var? α ε)

variable {α : Type u} {ε : Type v}

@[match_pattern]
def Ctx?.nil : Ctx? α ε := []

@[match_pattern]
def Ctx?.cons (Γ : Ctx? α ε) (v : Var? α ε) : Ctx? α ε := List.cons v Γ

@[match_pattern]
abbrev Ctx?.cons' (Γ : Ctx? α ε) (A : Ty α) (q : EQuant) (e : ε) : Ctx? α ε
  := Γ.cons ⟨A, q, e⟩

@[elab_as_elim, cases_eliminator]
def Ctx?.casesOn {motive : Ctx? α ε → Sort _} (Γ : Ctx? α ε)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive (.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v

@[elab_as_elim, induction_eliminator]
def Ctx?.inductionOn {motive : Ctx? α ε → Sort _} (Γ : Ctx? α ε)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive Γ → motive (Ctx?.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v (inductionOn Γ nil cons)

def Ctx?.length (Γ : Ctx? α ε) : ℕ := List.length Γ

@[simp]
theorem Ctx?.length_nil : Ctx?.length (.nil : Ctx? α ε) = 0 := rfl

@[simp]
theorem Ctx?.length_cons (Γ : Ctx? α ε) (v : Var? α ε)
  : Ctx?.length (Ctx?.cons Γ v) = Ctx?.length Γ + 1 := rfl

theorem Ctx?.length_cons' (Γ : Ctx? α ε) (A : Ty α) (q : EQuant) (e : ε)
  : Ctx?.length (Ctx?.cons' Γ A q e) = Ctx?.length Γ + 1 := rfl

@[simp]
def Ctx?.ety : Ctx? α ε → Ty α
  | .nil => Ty.unit
  | .cons Γ v => .tensor (Ctx?.ety Γ) v.ety

@[ext]
theorem Var?.ext {v w : Var? α ε}
  (h : v.ty = w.ty) (h' : v.q = w.q) (h'' : v.eff = w.eff) : v = w :=
  by cases v; cases w; cases h; cases h'; cases h''; rfl

abbrev Var?.unused (v : Var? α ε) : Prop := v.q = 0

@[simp]
theorem Var?.unused.eq_erase {v : Var? α ε} (h : v.unused) : v.erase = v
  := by cases v; cases h; rfl

abbrev Var?.used (v : Var? α ε) : Prop := 1 ≤ v.q

theorem Var?.used_iff (v : Var? α ε) : v.used ↔ ¬v.unused := EQuant.one_le_iff_ne_zero _

theorem Var?.unused_iff (v : Var? α ε) : v.unused ↔ ¬v.used := by simp [used_iff]

variable [HasQuant α]

open HasQuant

instance Var?.hasQuant : HasQuant (Var? α ε) where
  quant v := match v.q with | 0 => ⊤ | (q : Quant) => q ⊓ quant v.ty

instance Ctx?.hasQuant : HasQuant (Ctx? α ε) where
  quant Γ := Γ.foldr (λv q => q ⊓ quant v) ⊤

@[simp] theorem Ctx?.quant_nil : quant (.nil : Ctx? α ε) = ⊤ := rfl

@[simp]
theorem Ctx?.quant_cons (Γ : Ctx? α ε) (v : Var? α ε)
  : quant (Ctx?.cons Γ v) = quant Γ ⊓ quant v := rfl

abbrev Var?.del (v : Var? α ε) : Prop := IsAff v

abbrev Var?.copy (v : Var? α ε) : Prop := IsRel v

instance Var?.del.instZeroQuant (A : Ty α) (e : ε) : (⟨A, 0, e⟩ : Var? α ε).del
  := ⟨by simp [quant]⟩

instance Var?.copy.instZeroQuant (A : Ty α) (e : ε) : (⟨A, 0, e⟩ : Var? α ε).copy
  := ⟨by simp [quant]⟩

@[simp]
instance Var?.del.instErase (v : Var? α ε) : v.erase.del := ⟨by simp⟩

@[simp]
instance Var?.copy.instErase (v : Var? α ε) : v.erase.copy := ⟨by simp⟩

theorem Var?.del.q (v : Var? α ε) [hv : v.del] : 0 ≤ v.q := by
  cases v with | mk A q e => cases q using EQuant.casesZero with
  | zero => simp
  | rest => simp only [IsAff.is_aff_iff, quant, le_inf_iff] at hv; exact hv.1

theorem Var?.del.ty (v : Var? α ε) [hv : v.del] (h : v.used) : IsAff v.ty := by
  cases v with | mk A q e => cases q using EQuant.casesZero with
  | zero => simp at h
  | rest => simp only [IsAff.is_aff_iff, quant, le_inf_iff] at *; exact hv.2

theorem Var?.del_iff (v : Var? α ε) : v.del ↔ 0 ≤ v.q ∧ (v.used -> IsAff v.ty) := by
  cases v with | mk A q e => cases q using EQuant.casesZero with
  | zero => simp [quant, IsAff.is_aff_iff]
  | rest q => simp [quant, IsAff.is_aff_iff, quant]; intro _; cases q <;> decide

structure Var?.scopy (v : Var? α ε) : Prop where
  q : EQuant.copy ≤ v.q
  ty : IsRel v.ty

theorem Var?.scopy_iff (v : Var? α ε) : v.scopy ↔ (EQuant.copy ≤ v.q ∧ IsRel v.ty)
  := ⟨λh => ⟨h.1, h.2⟩, λh => ⟨h.1, h.2⟩⟩

theorem Var?.used.scopy {v : Var? α ε} (h : v.used) [hv : v.copy] : v.scopy := by
  cases v with | mk A q e => cases q using EQuant.casesZero with
  | zero => simp at h
  | rest => simp only [IsRel.is_rel_iff, quant, le_inf_iff] at hv; exact ⟨hv.1, ⟨hv.2⟩⟩

theorem Var?.unused.del {v : Var? α ε} (h : v.unused) : v.del
  := by simp only [unused] at h; simp [IsAff.is_aff_iff, quant, h]

theorem Var?.unused.copy {v : Var? α ε} (h : v.unused) : v.copy
  := by simp only [unused] at h; simp [IsRel.is_rel_iff, quant, h]

theorem Var?.scopy.copy {v : Var? α ε} (h : v.scopy) : v.copy := by
  cases v with | mk A q e => cases q using EQuant.casesZero with
  | zero => simp [IsRel.is_rel_iff, quant]
  | rest => simp [IsRel.is_rel_iff, quant]; constructor; exact h.q; exact h.ty.copy_le_quant

theorem Var?.copy_iff (v : Var? α ε) : v.copy ↔ (v.used -> v.scopy)
  := ⟨λ_ u => u.scopy, λh => if u : v.unused then u.copy else (h ((used_iff _).mpr u)).copy⟩

instance Var?.del.instTopQuant (A : Ty α) [IsAff A] (e : ε) : (⟨A, ⊤, e⟩ : Var? α ε).del
  := by simp [del_iff, *]

instance Var?.copy.instTopQuant (A : Ty α) [IsRel A] (e : ε) : (⟨A, ⊤, e⟩ : Var? α ε).copy
  := by simp [copy_iff, scopy_iff, *]

instance Var?.del.instDelQuant (A : Ty α) [IsAff A] (e : ε) : (⟨A, .del, e⟩ : Var? α ε).del
  := by simp [del_iff, *]

instance Var?.copy.instCopyQuant (A : Ty α) [IsRel A] (e : ε) : (⟨A, .copy, e⟩ : Var? α ε).copy
  := by simp [copy_iff, scopy_iff, *]

inductive Var?.PSSplit : Var? α ε → Var? α ε → Var? α ε → Type _
  | left (v) : PSSplit v v v.erase
  | right (v) : PSSplit v v.erase v
  | sboth {v} : v.scopy → PSSplit v v v

theorem Var?.PSSplit.left_unused {u v w : Var? α ε} (σ : u.PSSplit v w) (h : u.unused) : v.unused
  := by cases σ <;> first | assumption | rfl

theorem Var?.PSSplit.right_unused {u v w : Var? α ε} (σ : u.PSSplit v w) (h : u.unused) : w.unused
  := by cases σ <;> first | rfl | assumption

theorem Var?.PSSplit.used_of_left {u v w : Var? α ε} (σ : u.PSSplit v w) (h : v.used) : u.used
  := by cases σ <;> first | assumption | cases h

theorem Var?.PSSplit.used_of_right {u v w : Var? α ε} (σ : u.PSSplit v w) (h : w.used) : u.used
  := by cases σ <;> first | cases h | assumption

def Var?.PSSplit.both (v : Var? α ε) [h : IsRel v] : PSSplit v v v := if hv : v.used then
    PSSplit.sboth hv.scopy
  else by
    rw [<-Var?.unused_iff] at hv
    convert PSSplit.left v
    rw [hv.eq_erase]

def Var?.PSSplit.wkLeft {u v w : Var? α ε} (u' : Var? α ε)
  : u.PSSplit v w → Var? α ε
  | .left _ => if u.used then u' else u'.erase
  | .right _ => u'.erase
  | .sboth _ => if u.used then u' else u'.erase

@[simp]
theorem Var?.PSSplit.wkLeft_left {u' u : Var? α ε}
  : (PSSplit.left u).wkLeft u' = if u.used then u' else u'.erase := rfl

@[simp]
theorem Var?.PSSplit.wkLeft_right {u' u : Var? α ε}
  : (PSSplit.right u).wkLeft u' = u'.erase := rfl

@[simp]
theorem Var?.PSSplit.wkLeft_sboth {u' u : Var? α ε} (h : u.scopy)
  : (PSSplit.sboth h).wkLeft u' = if u.used then u' else u'.erase := rfl

def Var?.PSSplit.wkRight {u v w : Var? α ε} (u' : Var? α ε)
  : u.PSSplit v w → Var? α ε
  | .left _ => if u.used then u'.erase else u'
  | .right _ => u'
  | .sboth _ => u'

@[simp]
theorem Var?.PSSplit.wkRight_left {u' u : Var? α ε}
  : (PSSplit.left u).wkRight u' = if u.used then u'.erase else u' := rfl

@[simp]
theorem Var?.PSSplit.wkRight_right {u' u : Var? α ε}
  : (PSSplit.right u).wkRight u' = u' := rfl

@[simp]
theorem Var?.PSSplit.wkRight_sboth {u' u : Var? α ε} (h : u.scopy)
  : (PSSplit.sboth h).wkRight u' = u' := rfl

inductive Ctx?.PSSplit : Ctx? α ε → Ctx? α ε → Ctx? α ε → Type _ where
  | nil : Ctx?.PSSplit [] [] []
  | cons {Γ Δ Ξ v l r} (h : PSSplit Γ Δ Ξ) (hvw : v.PSSplit l r)
    : PSSplit (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)

theorem Ctx?.PSSplit.left_length {Γ Δ Ξ : Ctx? α ε} (h : Ctx?.PSSplit Γ Δ Ξ)
  : Ctx?.length Γ = Ctx?.length Δ
  := by induction h <;> simp [*]

theorem Ctx?.PSSplit.right_length {Γ Δ Ξ : Ctx? α ε} (h : Ctx?.PSSplit Γ Δ Ξ)
  : Ctx?.length Γ = Ctx?.length Ξ
  := by induction h <;> simp [*]

theorem Ctx?.PSSplit.target_length {Γ Δ Ξ : Ctx? α ε} (h : Ctx?.PSSplit Γ Δ Ξ)
  : Ctx?.length Δ = Ctx?.length Ξ := h.left_length.symm.trans h.right_length

theorem Ctx?.quant_le_of_quant_le_cons (Γ : Ctx? α ε) (h : q ≤ quant (Γ.cons v)) : q ≤ quant Γ
  := by simp at h; exact h.1

theorem Ctx?.quant_le_var_of_quant_le_cons (Γ : Ctx? α ε) (h : q ≤ quant (Γ.cons v)) : q ≤ quant v
  := by simp at h; exact h.2

instance Var?.copy.ety_rel (v : Var? α ε) [h : v.copy] : IsRel v.ety := by
  cases v with | mk A q e => cases q using EQuant.casesZero with
  | zero => simp only [ety]; infer_instance
  | rest => simp [quant, IsRel.is_rel_iff] at h; exact ⟨h.2⟩

instance Var?.del.ety_aff (v : Var? α ε) [h : v.del] : IsAff v.ety := by
  cases v with | mk A q e => cases q using EQuant.casesZero with
  | zero => simp only [ety]; infer_instance
  | rest => simp [quant, IsAff.is_aff_iff] at h; exact ⟨h.2⟩

abbrev Ctx?.copy (Γ : Ctx? α ε) : Prop := IsRel Γ

abbrev Ctx?.del (Γ : Ctx? α ε) : Prop := IsAff Γ

@[simp]
instance Ctx?.nil_copy : (.nil : Ctx? α ε).copy := ⟨by simp⟩

@[simp]
instance Ctx?.nil_del : (.nil : Ctx? α ε).del := ⟨by simp⟩

@[simp]
theorem Ctx?.cons_copy_iff (Γ : Ctx? α ε) (v : Var? α ε) : (Γ.cons v).copy ↔ Γ.copy ∧ v.copy
  := ⟨λ⟨h⟩ => by simp at h; exact ⟨⟨h.1⟩, ⟨h.2⟩⟩, λ⟨⟨hΓ⟩, ⟨hv⟩⟩ => ⟨by simp [*]⟩⟩

theorem Ctx?.copy.tail (Γ : Ctx? α ε) (v : Var? α ε) [h : (Γ.cons v).copy] : Γ.copy
  := by rw [cons_copy_iff] at h; exact h.1

theorem Ctx?.copy.head (Γ : Ctx? α ε) (v : Var? α ε) [h : (Γ.cons v).copy] : v.copy
  := by rw [cons_copy_iff] at h; exact h.2

instance Ctx?.copy.cons (Γ : Ctx? α ε) (v : Var? α ε) [Γ.copy] [v.copy] : (Γ.cons v).copy
  := ⟨by simp [cons_copy_iff, *]⟩

@[simp]
theorem Ctx?.cons_del_iff (Γ : Ctx? α ε) (v : Var? α ε) : (Γ.cons v).del ↔ Γ.del ∧ v.del
  := ⟨λ⟨h⟩ => by simp at h; exact ⟨⟨h.1⟩, ⟨h.2⟩⟩, λ⟨⟨hΓ⟩, ⟨hv⟩⟩ => ⟨by simp [*]⟩⟩

theorem Ctx?.del.tail (Γ : Ctx? α ε) (v : Var? α ε) [h : (Γ.cons v).del] : Γ.del
  := by rw [cons_del_iff] at h; exact h.1

theorem Ctx?.del.head (Γ : Ctx? α ε) (v : Var? α ε) [h : (Γ.cons v).del] : v.del
  := by rw [cons_del_iff] at h; exact h.2

instance Ctx?.del.cons (Γ : Ctx? α ε) (v : Var? α ε) [Γ.del] [v.del] : (Γ.cons v).del
  := ⟨by simp [cons_del_iff, *]⟩

instance Ctx?.ety_rel_of_copy {Γ : Ctx? α ε} [h : Γ.copy] : IsRel (Ctx?.ety Γ) := by
  generalize h = h
  induction Γ with
  | nil => constructor; simp [ety]
  | cons Γ v I =>
    have _ := I (copy.tail Γ v)
    have _ := copy.head Γ v
    simp only [ety]
    apply IsRel.tensor

instance Ctx?.ety_aff_of_del {Γ : Ctx? α ε} [h : Γ.del] : IsAff (Ctx?.ety Γ) := by
  generalize h = h
  induction Γ with
  | nil => constructor; simp [ety]
  | cons Γ v I =>
    have _ := I (del.tail Γ v)
    have _ := del.head Γ v
    simp only [ety]
    apply IsAff.tensor

def Ctx?.both (Γ : Ctx? α ε) : [Γ.copy] → Γ.PSSplit Γ Γ := λ{_} => match Γ with
  | .nil => .nil
  | .cons Γ v => .cons (have _ := copy.tail Γ v; Γ.both) (have _ := copy.head Γ v; .both v)

variable [PartialOrder ε]

structure Var?.Wk (v w : Var? α ε) : Prop where
  ty : v.ty = w.ty
  q : w.q ≤ v.q
  eff : v.eff ≤ w.eff
  unused_del : w.unused → v.del

theorem Var?.wk_eff (A : Ty α) (q : EQuant) {e e' : ε} (h : e ≤ e') : Var?.Wk ⟨A, q, e⟩ ⟨A, q, e'⟩
  := ⟨rfl, le_refl _, h, λh => by convert h.del using 0; simp [del_iff]⟩

instance Var?.instLE : LE (Var? α ε) := ⟨Wk⟩

theorem Var?.erase_mono {v w : Var? α ε} (h : v ≤ w) : v.erase ≤ w.erase := by
  cases v with | mk A q e => cases w with | mk A' q' e' =>
    exact ⟨h.ty, le_refl _, h.eff, λ_ => inferInstance⟩

theorem Var?.used.anti {v w : Var? α ε} (h : v ≤ w) (hw : w.used) : v.used := hw.trans h.q

theorem Var?.unused.mono {v w : Var? α ε} (h : v ≤ w) : (hv : v.unused) → w.unused
  := by simp only [unused_iff, not_imp_not]; exact used.anti h

theorem Var?.del.anti {v w : Var? α ε} (h : v ≤ w) [hw : w.del] : v.del := open Classical in
  if hw' : w.used then
    by rw [del_iff] at *; exact ⟨hw.1.trans h.q, λ_ => h.ty ▸ hw.2 hw'⟩
  else
    h.unused_del ((unused_iff w).mpr hw')

theorem Var?.scopy.anti {v w : Var? α ε} (h : v ≤ w) (hw : w.scopy) : v.scopy where
  q := hw.q.trans h.q
  ty := h.ty ▸ hw.ty

theorem Var?.used.scopy_anti {v w : Var? α ε} (h : v ≤ w) (hw' : w.used) [hw : w.copy] : v.scopy
  := by rw [copy_iff] at *; exact (hw hw').anti h

theorem Var?.copy.anti {v w : Var? α ε} (h : v ≤ w) [hw : IsRel w] (hw' : w.used) : v.copy
  := (hw'.scopy_anti h).copy

instance Var?.instPartialOrder : PartialOrder (Var? α ε) where
  le_refl _ := ⟨rfl, le_refl _, le_refl _, λh => h.del⟩
  le_trans _ _ _ h h' :=
    ⟨h.ty.trans h'.ty, h'.q.trans h.q, h.eff.trans h'.eff, λx => (x.del.anti h').anti h⟩
  le_antisymm _ _ h h' := ext h.ty (le_antisymm h'.q h.q) (le_antisymm h.eff h'.eff)

theorem Var?.Wk.ety_aff_zero {B : Ty α} {e : ε} (h : v ≤ Var?.mk B 0 e)
  : IsAff v.ety := del.ety_aff _ (h := del.anti h)

theorem Var?.Wk.ety_eq_quant {B : Ty α} {q : Quant} {e : ε} (h : v ≤ Var?.mk B q e)
  : v.ety = B := by
  cases v with | mk A q' e' => cases q' using EQuant.casesZero with
  | zero => cases h.q using EQuant.le.casesLE
  | rest => cases h.ty; rfl

theorem Var?.Wk.ety_eq_used {v w : Var? α ε} (h : v ≤ w) (hw : w.used) : v.ety = w.ety := by
  cases w with | mk A q e =>
    cases q using EQuant.casesZero with
    | zero => cases hw
    | rest => rw [ety_eq_quant h]

inductive Ctx?.PWk : Ctx? α ε → Ctx? α ε → Prop where
  | nil : Ctx?.PWk .nil .nil
  | cons {Γ Δ v w} (h : Ctx?.PWk Γ Δ) (hvw : v ≤ w) : Ctx?.PWk (Ctx?.cons Γ v) (Ctx?.cons Δ w)

theorem Ctx?.PWk.head {Γ Δ v w} (h : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w)) : v ≤ w
  := match h with | Ctx?.PWk.cons _ hvw => hvw

theorem Ctx?.PWk.tail {Γ Δ v w} (h : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w)) : PWk Γ Δ
  := match h with | Ctx?.PWk.cons h _ => h

@[simp]
theorem Ctx?.PWk.cons_iff {Γ Δ v w} : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w) ↔ PWk Γ Δ ∧ v ≤ w
  := ⟨λ h => ⟨Ctx?.PWk.tail h, Ctx?.PWk.head h⟩, λ ⟨h, h'⟩ => Ctx?.PWk.cons h h'⟩

def Ctx?.PWk.inductionOn {Γ Δ} (h : PWk Γ Δ) {motive : (Γ Δ : Ctx? α ε) → PWk Γ Δ → Sort _}
  (nil : motive .nil .nil .nil)
  (cons : ∀ {Γ Δ v w} (h : PWk Γ Δ) (hvw : v ≤ w),
    motive Γ Δ h →
    motive (Ctx?.cons Γ v) (Ctx?.cons Δ w) (Ctx?.PWk.cons h hvw))
  : motive Γ Δ h := match Γ, Δ, h with
  | .nil, .nil, _ => nil
  | .cons _ _, .cons _ _, h => cons h.tail h.head (inductionOn h.tail nil cons)

@[simp]
theorem Ctx?.PWk.refl (Γ : Ctx? α ε) : PWk Γ Γ := by induction Γ <;> simp [Ctx?.PWk.nil, *]

theorem Ctx?.PWk.trans {Γ Δ Ξ : Ctx? α ε} (h : PWk Γ Δ) (h' : PWk Δ Ξ) : PWk Γ Ξ := by
  induction h generalizing Ξ <;> cases h'
  simp only [refl]
  simp only [cons_iff, true_and, *]
  apply le_trans <;> assumption

theorem Ctx?.PWk.antisymm {Γ Δ : Ctx? α ε} (h : PWk Γ Δ) (h' : PWk Δ Γ) : Γ = Δ := by
  induction h with
  | nil => rfl
  | cons h hvw I => cases h' with
  | cons h' hwv => rw [I h', le_antisymm hvw hwv]

theorem Ctx?.PWk.length {Γ Δ : Ctx? α ε} (h : PWk Γ Δ) : Ctx?.length Γ = Ctx?.length Δ
  := by induction h <;> simp [*]

inductive Ctx?.Wk : Ctx? α ε → Ctx? α ε → Type _ where
  | nil : Ctx?.Wk .nil .nil
  | cons {Γ Δ v w} (h : Ctx?.Wk Γ Δ) (hvw : v ≤ w) : Ctx?.Wk (Ctx?.cons Γ v) (Ctx?.cons Δ w)
  | skip {Γ Δ v} (h : Ctx?.Wk Γ Δ) (hv : v.del) : Ctx?.Wk (Ctx?.cons Γ v) Δ

@[match_pattern]
abbrev Ctx?.Wk.scons {Γ Δ : Ctx? α ε} (v : Var? α ε) (ρ : Γ.Wk Δ)
  := ρ.cons (le_refl v)

theorem Ctx?.Wk.length {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) : Ctx?.length Δ ≤ Ctx?.length Γ
  := by induction h <;> simp <;> omega

def Ctx?.PWk.toWk {Γ Δ : Ctx? α ε} (h : PWk Γ Δ) : Wk Γ Δ
  := h.inductionOn (motive := λΓ Δ _ => Wk Γ Δ) .nil (λ_ h m => .cons m h)

theorem Ctx?.Wk.toPWk {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (h' : Γ.length = Δ.length) : Γ.PWk Δ
  := by induction h with
  | nil => exact .nil
  | cons h v I => exact .cons (I (by convert h' using 0; simp)) v
  | skip h =>
    have hl := h.length
    rw [<-h', length_cons] at hl
    omega

theorem Ctx?.Wk.antisymm {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Γ) : Γ = Δ :=
  have hl := le_antisymm h'.length h.length
  PWk.antisymm (h.toPWk hl) (h'.toPWk (hl.symm))

-- toPWk is a faithful functor
theorem Ctx?.Wk.eq_pwk {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (h' : Γ.length = Δ.length)
  : h = (h.toPWk h').toWk := by induction h with
  | nil => rfl
  | cons h v I =>
    rw [I]
    rfl
    convert h' using 0
    simp
  | skip h =>
    have hl := h.length
    rw [<-h', length_cons] at hl
    omega

def Ctx?.Wk.refl (Γ : Ctx? α ε) : Wk Γ Γ := (Ctx?.PWk.refl Γ).toWk

theorem Ctx?.Wk.eq_refl {Γ : Ctx? α ε} (h : Wk Γ Γ) : h = Wk.refl Γ := eq_pwk h rfl

def Ctx?.Wk.comp {Γ Δ Ξ : Ctx? α ε} : Wk Γ Δ → Wk Δ Ξ → Wk Γ Ξ
  | .nil, .nil => .nil
  | .cons h hv, .cons h' hv' => .cons (h.comp h') (hv.trans hv')
  | .cons h hv, .skip h' hv' => .skip (h.comp h') (Var?.del.anti hv)
  | .skip h hv, h' => .skip (h.comp h') hv

theorem Ctx?.Wk.comp_assoc {Γ Δ Ξ Θ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (h'' : Wk Ξ Θ)
  : h.comp (h'.comp h'') = (h.comp h').comp h'' := by induction h generalizing Ξ Θ with
  | nil => cases h'; cases h''; rfl
  | cons _ _ I => cases h' <;> cases h'' <;> simp [comp, I]
  | skip _ _ I => simp [comp, I]

@[simp]
def Ctx?.Wk.ix {Γ Δ : Ctx? α ε} : Wk Γ Δ → ℕ → ℕ
  | .nil => id
  | .cons h _ => Nat.liftWk h.ix
  | .skip h _ => Nat.stepWk h.ix

instance Ctx?.Wk.coeFunRen {Γ Δ : Ctx? α ε} : CoeFun (Wk Γ Δ) (λ_ => ℕ → ℕ) := ⟨ix⟩

@[simp]
theorem Ctx?.Wk.ix_increasing {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (i : ℕ) : i ≤ h i := by
  induction h generalizing i with
  | nil => simp [ix]
  | cons _ _ I => cases i <;> simp [ix, *]
  | skip _ _ I => simp [ix]; have I := I i; omega

@[simp]
theorem Ctx?.Wk.ix_comp_applied {Γ Δ Ξ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (i : ℕ)
  : (h.comp h') i = h (h' i) := by induction h generalizing Ξ i with
  | nil => cases h'; rfl
  | cons _ _ I => cases h' <;> cases i <;> simp [comp, ix, I]
  | skip _ _ I => simp [comp, ix, I]

theorem Ctx?.Wk.ix_comp {Γ Δ Ξ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ)
  : (h.comp h').ix = h.ix ∘ h'.ix := funext (λi => Wk.ix_comp_applied h h' i)

theorem Ctx?.Wk.ix_length_eq_applied {Γ Δ : Ctx? α ε}
  (h : Γ.Wk Δ) (hl : Γ.length = Δ.length) (i : ℕ) : h i = i := by induction h generalizing i with
  | nil => rfl
  | cons _ _ I =>
    cases i; rfl; simp only [ix, Nat.liftWk_succ, add_left_inj]; apply I; convert hl using 0; simp
  | skip h _ => have hl' := h.length; rw [<-hl] at hl'; simp at hl'

theorem Ctx?.Wk.ix_length_eq {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) (hl : Γ.length = Δ.length)
  : h.ix = id := funext (λi => ix_length_eq_applied h hl i)

theorem Ctx?.Wk.ix_refl {Γ : Ctx? α ε} (h : Γ.Wk Γ) : h.ix = id := ix_length_eq _ rfl

-- TODO: ix is an injection...

theorem Ctx?.Wk.ix_bounded {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) (i : ℕ)
  (hi : i < Δ.length) : h.ix i < Γ.length
  := by induction h generalizing i with
  | nil => simp at hi
  | cons _ _ I =>
    cases i
    · simp [ix]
    · simp only [ix, Nat.liftWk_succ, length_cons, add_lt_add_iff_right]
      apply I; convert hi using 0; simp
  | skip _ _ I => simp [ix, *]

def Ctx?.Wk.skips {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) : ℕ := h 0

--TODO: minimize and report because this is a _sin_
def Ctx?.drop (Γ : Ctx? α ε) [h : Γ.del] : Wk Γ .nil := (λh => match Γ with
  | .nil => .nil
  | .cons Γ _ => have _ := h.tail; .skip Γ.drop h.head) h

@[simp]
theorem Ctx?.Wk.drop_nil : (.nil : Ctx? α ε).drop = .nil := rfl

@[simp]
theorem Ctx?.Wk.drop_cons (Γ : Ctx? α ε) [hΓ : Γ.del] (v : Var? α ε) [hv : v.del]
  : (Ctx?.cons Γ v).drop = Γ.drop.skip inferInstance := rfl

theorem Ctx?.Wk.drop_del {Γ : Ctx? α ε} (w : Γ.Wk .nil) : Γ.del := by
  induction Γ <;> cases w <;> simp; constructor <;> apply_assumption; assumption

theorem Ctx?.wk_nil_eq_drop {Γ : Ctx? α ε} (w : Γ.Wk .nil) : w = Γ.drop (h := w.drop_del) := by
  induction Γ <;> cases w <;> rw [drop]; simp; apply_assumption

theorem Ctx?.wk_nil_unique {Γ : Ctx? α ε} (w w' : Γ.Wk .nil) : w = w' := by
  rw [wk_nil_eq_drop w, wk_nil_eq_drop w']

theorem Ctx?.del.wk {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) [hΔ : Δ.del] : Γ.del := (λhΔ => by
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

def Ctx?.choose_drop (Γ : Ctx? α ε) (h : Nonempty (Γ.Wk .nil)) : Γ.Wk .nil :=
  have _ : Γ.del := let ⟨h⟩ := h; h.drop_del; Γ.drop

def Var?.Ix (Γ : Ctx? α ε) (v : Var? α ε) : Type _ := Γ.Wk [v]

@[match_pattern]
def Var?.zero_le {Γ : Ctx? α ε} (x : Γ.Wk .nil) {v w : Var? α ε} (h : v ≤ w) : Ix (Γ.cons v) w
  := x.cons h

@[match_pattern]
abbrev Var?.zero {Γ : Ctx? α ε} (x : Γ.Wk .nil) (v : Var? α ε) : Ix (Γ.cons v) v
  := zero_le x (le_refl v)

@[match_pattern]
def Var?.Ix.succ {Γ : Ctx? α ε} (v : Var? α ε) [h : v.del] {w} (x : Ix Γ w) : Ix (Γ.cons v) w
  := x.skip h

@[elab_as_elim, cases_eliminator]
def Var?.Ix.casesOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx? α ε} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} (v : Var? α ε) (_ : v.del) {w} (x : Ix Γ w), motive (succ v x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ _ _ x

@[elab_as_elim, induction_eliminator]
def Var?.Ix.inductionOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx? α ε} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} {v : Var? α ε} (h : v.del) {w} (x : Ix Γ w), motive x → motive (succ v (h := h) x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ hv x (inductionOn x zero_le succ)

def Var?.Ix.ix {Γ : Ctx? α ε} {v} (x : Ix Γ v) : ℕ := x.skips

@[simp]
theorem Var?.ix_zero_le {Γ : Ctx? α ε} {v w : Var? α ε} (h : v ≤ w) (x : Γ.Wk .nil)
  : (zero_le x h).ix = 0 := rfl

@[simp]
theorem Var?.Ix.ix_succ {Γ : Ctx? α ε} (v : Var? α ε) [h : v.del] {w} (x : Ix Γ w)
  : (succ v x).ix = x.ix + 1 := rfl

def Var?.Ix.wk {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : Ix Γ v := h.comp x

theorem Var?.Ix.wk_wk {Γ Δ Ξ : Ctx? α ε} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : (x.wk h').wk h = x.wk (h.comp h') := Ctx?.Wk.comp_assoc h h' x

theorem Var?.Ix.wk_comp {Γ Δ Ξ : Ctx? α ε} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : x.wk (h.comp h') = (x.wk h').wk h := (x.wk_wk h h').symm

@[simp]
theorem Var?.Ix.succ_wk_cons {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ)
  {v v' : Var? α ε} (hv : v ≤ v') [hv' : IsAff v'] {w} (x : Ix Δ w)
  : (succ _ x).wk (h.cons hv) = (succ _ (h := del.anti hv) (x.wk h)) := rfl

@[simp]
theorem Var?.Ix.wk_skip {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ)
  (v : Var? α ε) [hv : IsAff v] {w} (x : Ix Δ w)
  : x.wk (h.skip hv) = (x.wk h).succ v := rfl

@[simp]
theorem Var?.Ix.ix_wk {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : (x.wk h).ix = h.ix x.ix
  := by rw [ix, Ctx?.Wk.skips, wk, Ctx?.Wk.ix_comp]; rfl

theorem Var?.Ix.ix_wk_le {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : x.ix ≤ (x.wk h).ix
  := by simp

-- TODO: ix is an injection on variables...

inductive Ctx?.At (v : Var? α ε) : Ctx? α ε → ℕ → Prop where
  | here {Γ} (d : Ctx?.Wk Γ .nil) {w} : w ≤ v → Ctx?.At v (Ctx?.cons Γ w) 0
  | there {Γ w n} (x : Ctx?.At v Γ n) (hw : w.del) : Ctx?.At v (Ctx?.cons Γ w) (n + 1)

theorem Ctx?.At.zero_cons_head {Γ : Ctx? α ε} {v} (h : (Γ.cons w).At v 0) : w ≤ v
  := by cases h; assumption

def Ctx?.At.zero_cons_tail {Γ : Ctx? α ε} {v} (h : (Γ.cons w).At v 0) : Γ.Wk .nil
  := Γ.choose_drop (by cases h; constructor; assumption)

theorem Ctx?.At.succ_cons_head {Γ : Ctx? α ε} {v w} (h : (Γ.cons w).At v (n + 1)) : w.del
  := by cases h; assumption

theorem Ctx?.At.succ_cons_tail {Γ : Ctx? α ε} {v w} (h : (Γ.cons w).At v (n + 1)) : Γ.At v n
  := by cases h; assumption

theorem Ctx?.At.succ_cons_iff (Γ : Ctx? α ε) (v w) : (Γ.cons w).At v (n + 1) ↔ w.del ∧ Γ.At v n
  := ⟨λh => ⟨h.succ_cons_head, h.succ_cons_tail⟩, λ⟨h, h'⟩ => At.there h' h⟩

@[elab_as_elim, induction_eliminator]
def Ctx?.At.inductionOn {v : Var? α ε} {motive : ∀ (Γ n), Ctx?.At v Γ n → Sort _}
  (h : Ctx?.At v Γ n)
  (here : ∀ (Γ : Ctx? α ε) (d : Γ.Wk .nil) (w) (hw : w ≤ v), motive (Γ.cons w) 0 (here d hw))
  (there : ∀ (Γ) (w : Var? α ε) (n) (x : Ctx?.At v Γ n) (hw : w.del),
    motive Γ n x → motive (Γ.cons w) (n + 1) (there x hw))
  : motive Γ n h := match Γ, n, h with
  | .cons Γ w, 0, h => here Γ h.zero_cons_tail w h.zero_cons_head
  | .cons Γ w, n + 1, h
    => there Γ w n h.succ_cons_tail h.succ_cons_head (h.succ_cons_tail.inductionOn here there)

theorem Ctx?.At.wkOut {v : Var? α ε} {Γ : Ctx? α ε} {n} (h : Γ.At v n) (h' : v ≤ w)
  : Γ.At w n := by induction h <;> constructor <;> (try apply le_trans) <;> assumption

theorem Ctx?.At.wkIn {Γ Δ : Ctx? α ε} (w : Γ.Wk Δ) {v : Var? α ε} {n} (h : Δ.At v n)
  : Γ.At v (w n) := by induction w generalizing n with
  | nil => cases h
  | skip w hv I => constructor <;> apply_assumption; assumption
  | cons w hv I => cases h with
  | here => constructor; (apply Wk.comp <;> assumption); (apply le_trans <;> assumption)
  | there => constructor; (apply I; assumption); (exact Var?.del.anti hv)

def Ctx?.At.ix {Γ : Ctx? α ε} {v n} (h : Γ.At v n) : v.Ix Γ
  := h.inductionOn (λ_ d _ h => Var?.zero_le d h) (λ_ _ _ _ _ I => I.succ _)

@[simp]
theorem Ctx?.At.ix_ix {Γ : Ctx? α ε} {v n} (h : Γ.At v n) : h.ix.ix = n
  := by induction h <;> simp [ix, inductionOn]; assumption

theorem Var?.Ix.at {Γ : Ctx? α ε} {v} (x : Ix Γ v) : Γ.At v x.ix
  := by induction x <;> constructor <;> assumption

-- TODO: so therefore at_ix is just the identity

inductive Var?.PSplit : Var? α ε → Var? α ε → Var? α ε → Type _
  | left {v w} (h : v ≤ w) (e) : PSplit v w ⟨v.ty, 0, e⟩
  | right {v w} (h : v ≤ w) (e) : PSplit v ⟨v.ty, 0, e⟩ w
  | sboth {u v w} : u.scopy → u ≤ v → u ≤ w → PSplit u v w

inductive Ctx?.PSplit : Ctx? α ε → Ctx? α ε → Ctx? α ε → Type _ where
  | nil : Ctx?.PSplit [] [] []
  | cons {Γ Δ Ξ v l r} (h : PSplit Γ Δ Ξ) (hvw : v.PSplit l r)
    : PSplit (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)

def Var?.PSSplit.toPSplit {u v w : Var? α ε} (h : u.PSSplit v w) : u.PSplit v w := match h with
  | Var?.PSSplit.left _ => Var?.PSplit.left (le_refl _) _
  | Var?.PSSplit.right _ => Var?.PSplit.right (le_refl _) _
  | Var?.PSSplit.sboth hu => Var?.PSplit.sboth hu (le_refl _) (le_refl _)

def Ctx?.PSSplit.toPSplit {Γ Δ Ξ : Ctx? α ε} : Ctx?.PSSplit Γ Δ Ξ → Ctx?.PSplit Γ Δ Ξ
  | .nil => .nil
  | .cons h hvw => .cons h.toPSplit hvw.toPSplit

def Var?.PSSplit.wk {u' u v w : Var? α ε} (ρ : u' ≤ u) (σ : u.PSSplit v w) :
  u'.PSSplit (σ.wkLeft u') (σ.wkRight u') := match u, σ with
  | ⟨A, (q : Quant), e⟩, .left _ => .left _
  | ⟨A, (q : Quant), e⟩, .right _ => .right _
  | ⟨A, 0, e⟩, .left _ | ⟨A, 0, e⟩, .right _ => .right _
  | ⟨A, (q : Quant), e⟩, .sboth h => .sboth (h.anti ρ)

@[simp]
theorem Var?.PSSplit.wk_left_quant {u' : Var? α ε} {A : Ty α} {q : Quant} {e : ε}
  (ρ : u' ≤ ⟨A, q, e⟩) : (PSSplit.left ⟨A, q, e⟩).wk ρ = .left u' := rfl

@[simp]
theorem Var?.PSSplit.wk_right_quant {u' : Var? α ε} {A : Ty α} {q : Quant} {e : ε}
  (ρ : u' ≤ ⟨A, q, e⟩) : (PSSplit.right ⟨A, q, e⟩).wk ρ = .right u' := rfl

@[simp]
theorem Var?.PSSplit.wk_left_zero {u' : Var? α ε} {A : Ty α} {e : ε}
  (ρ : u' ≤ ⟨A, 0, e⟩) : (PSSplit.left ⟨A, 0, e⟩).wk ρ = .right u' := rfl

@[simp]
theorem Var?.PSSplit.wk_right_zero {u' : Var? α ε} {A : Ty α} {e : ε}
  (ρ : u' ≤ ⟨A, 0, e⟩) : (PSSplit.right ⟨A, 0, e⟩).wk ρ = .right u' := rfl

@[simp]
theorem Var?.PSSplit.wk_sboth_quant {u' : Var? α ε} {A : Ty α} {q : Quant} {e : ε}
  (ρ : u' ≤ ⟨A, q, e⟩) (h : (Var?.mk A q e).scopy)
  : (PSSplit.sboth h).wk ρ = PSSplit.sboth (h.anti ρ) := rfl

@[simp]
theorem Var?.PSSplit.leftWk {u' u v w : Var? α ε} (ρ : u' ≤ u) (σ : u.PSSplit v w)
  : (σ.wkLeft u') ≤ v := by cases u with | mk A q e =>
    cases q using EQuant.casesZero <;> cases σ <;> first | exact ρ | exact (erase_mono ρ)

@[simp]
theorem Var?.PSSplit.rightWk {u' u v w : Var? α ε} (ρ : u' ≤ u) (σ : u.PSSplit v w)
  : (σ.wkRight u') ≤ w := by cases u with | mk A q e =>
    cases q using EQuant.casesZero <;> cases σ <;> first | exact ρ | exact (erase_mono ρ)

@[simp]
theorem Var?.PSSplit.leftWk_copy {u' u v w : Var? α ε}
  (ρ : u' ≤ u) (σ : u.PSSplit v w) [hv : v.copy]
  : (σ.wkLeft u').copy := by cases u with | mk A q e =>
    cases q using EQuant.casesZero with
    | zero => cases σ <;> simp
    | rest q => cases σ <;> simp <;> apply copy.anti (hw := _) ρ <;> simp [*]

@[simp]
def Ctx?.PSSplit.wkLeft {Γ' Γ Δ Ξ : Ctx? α ε}
  : Γ'.Wk Γ → Γ.PSSplit Δ Ξ → Ctx? α ε
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkLeft ρ σ).cons v.erase
  | .cons (v := v) ρ _, .cons σ hlr => (wkLeft ρ σ).cons (hlr.wkLeft v)

@[simp]
def Ctx?.PSSplit.wkRight {Γ' Γ Δ Ξ : Ctx? α ε}
  : Γ'.Wk Γ → Γ.PSSplit Δ Ξ → Ctx? α ε
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkRight ρ σ).cons v
  | .cons (v := v) ρ _, .cons σ hlr => (wkRight ρ σ).cons (hlr.wkRight v)

@[simp]
def Ctx?.PSSplit.leftWk {Γ' Γ Δ Ξ : Ctx? α ε}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.PSSplit Δ Ξ) → (σ.wkLeft ρ).Wk Δ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.leftWk ρ) inferInstance
  | .cons ρ hvw, .cons σ hlr => .cons (σ.leftWk ρ) (hlr.leftWk hvw)

@[simp]
def Ctx?.PSSplit.rightWk {Γ' Γ Δ Ξ : Ctx? α ε}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.PSSplit Δ Ξ) → (σ.wkRight ρ).Wk Ξ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.rightWk ρ) inferInstance
  | .cons ρ hvw, .cons σ hlr => .cons (σ.rightWk ρ) (hlr.rightWk hvw)

@[simp]
theorem Ctx?.PSSplit.ix_leftWk {Γ' Γ Δ Ξ : Ctx? α ε} (ρ : Γ'.Wk Γ) (σ : Γ.PSSplit Δ Ξ)
  : (σ.leftWk ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.PSSplit.leftWk_applied {Γ' Γ Δ Ξ : Ctx? α ε} (ρ : Γ'.Wk Γ) (σ : Γ.PSSplit Δ Ξ) (i : ℕ)
  : (σ.leftWk ρ) i = ρ i := by simp

@[simp]
theorem Ctx?.PSSplit.ix_rightWk {Γ' Γ Δ Ξ : Ctx? α ε} (ρ : Γ'.Wk Γ) (σ : Γ.PSSplit Δ Ξ)
  : (σ.rightWk ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.PSSplit.rightWk_applied {Γ' Γ Δ Ξ : Ctx? α ε} (ρ : Γ'.Wk Γ) (σ : Γ.PSSplit Δ Ξ) (i : ℕ)
  : (σ.rightWk ρ) i = ρ i := by simp

@[simp]
def Ctx?.PSSplit.wk {Γ' Γ Δ Ξ : Ctx? α ε}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.PSSplit Δ Ξ) → Γ'.PSSplit (σ.wkLeft ρ) (σ.wkRight ρ)
  | .nil, .nil => .nil
  | .skip (v := ⟨A, q, e⟩) ρ _, σ => .cons (σ.wk ρ) (.right ..)
  | .cons ρ hvw, .cons σ hlr => .cons (σ.wk ρ) (hlr.wk hvw)

-- Since all unused variables go on the right, we have the following useful theorem:
def Ctx?.PSSplit.wkLeft_copy {Γ' Γ Δ Ξ : Ctx? α ε} (ρ : Γ'.Wk Γ) (σ : Γ.PSSplit Δ Ξ) [hΔ : Δ.copy]
  : (σ.wkLeft ρ).copy
  := by induction ρ generalizing Δ Ξ with
  | nil => simp
  | skip ρ hv I => simp [*]
  | cons ρ hvw I =>
    cases σ with | cons _ hlr =>
    have _ := hΔ.tail
    simp only [wkLeft, cons_copy_iff, I, true_and]
    cases hlr <;> simp
    <;> split
    <;> first | simp | (have _ := hΔ.head; apply Var?.copy.anti hvw; assumption)
