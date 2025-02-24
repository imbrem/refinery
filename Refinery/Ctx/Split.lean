import Refinery.Ctx.Basic

namespace Refinery

variable [HasQuant α]

inductive Var?.Split : Var? α → Var? α → Var? α → Type _
  | neither {A q} : del ⟨A, q⟩ → Split ⟨A, q⟩ ⟨A, 0⟩ ⟨A, 0⟩
  | left (A q) : Split ⟨A, q⟩ ⟨A, q⟩ ⟨A, 0⟩
  | right (A q) : Split ⟨A, q⟩ ⟨A, 0⟩ ⟨A, q⟩
  | both {u} : u.copy → Split u u u

abbrev Var?.splitN (v : Var? α) [hv : v.del] : v.Split v.erase v.erase := .neither hv

abbrev Var?.splitL (v : Var? α) : v.Split v v.erase := .left v.ty v.q

abbrev Var?.splitR (v : Var? α) : v.Split v.erase v := .right v.ty v.q

abbrev Var?.splitB (v : Var? α) [hv : v.copy] : v.Split v v := .both hv

theorem Var?.Split.left_unused {u v w : Var? α} (σ : u.Split v w) (h : u.unused) : v.unused
  := by cases σ <;> first | assumption | rfl

theorem Var?.Split.right_unused {u v w : Var? α} (σ : u.Split v w) (h : u.unused) : w.unused
  := by cases σ <;> first | rfl | assumption

theorem Var?.Split.used_of_left {u v w : Var? α} (σ : u.Split v w) (h : v.used) : u.used
  := by cases σ <;> first | assumption | cases h

theorem Var?.Split.used_of_right {u v w : Var? α} (σ : u.Split v w) (h : w.used) : u.used
  := by cases σ <;> first | cases h | assumption

theorem Var?.Split.erase_eq_left {u v w : Var? α} (h : u.Split v w)
  : u.erase = v.erase := by cases h <;> simp [*]

theorem Var?.Split.erase_eq_right {u v w : Var? α} (h : u.Split v w)
  : u.erase = w.erase := by cases h <;> simp [*]

theorem Var?.Split.erase_eq_both {u v w : Var? α} (h : u.Split v w)
  : v.erase = w.erase := by cases h <;> simp [*]

inductive Ctx?.Split : Ctx? α → Ctx? α → Ctx? α → Type _ where
  | nil : Ctx?.Split .nil .nil .nil
  | cons {Γ Δ Ξ v l r} (h : Split Γ Δ Ξ) (hvw : v.Split l r)
    : Split (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)

def Var?.Split.hasLeft {u v w : Var? α} : u.Split v w → Bool
  | .left _ _ => true | .both _ => true | _ => false

@[simp]
theorem Var?.Split.hasLeft_neither {A q} [hA : Var?.del ⟨A, q⟩]
  : (Split.neither (α := α) hA).hasLeft = false := rfl

@[simp]
theorem Var?.Split.hasLeft_left {A q} : (Split.left (α := α) A q).hasLeft = true := rfl

@[simp]
theorem Var?.Split.hasLeft_right {A q} : (Split.right (α := α) A q).hasLeft = false := rfl

@[simp]
theorem Var?.Split.hasLeft_both {u : Var? α} [hu : u.copy] : (Split.both hu).hasLeft = true := rfl

def Var?.Split.hasRight {u v w : Var? α} : u.Split v w → Bool
  | .right _ _ => true | .both _ => true | _ => false

@[simp]
theorem Var?.Split.hasRight_neither {A q} [hA : Var?.del ⟨A, q⟩]
  : (Split.neither (α := α) hA).hasRight = false := rfl

@[simp]
theorem Var?.Split.hasRight_left {A q} : (Split.left (α := α) A q).hasRight = false := rfl

@[simp]
theorem Var?.Split.hasRight_right {A q} : (Split.right (α := α) A q).hasRight = true := rfl

@[simp]
theorem Var?.Split.hasRight_both {u : Var? α} [hu : u.copy] : (Split.both hu).hasRight = true := rfl

def Var?.Split.wkLeft {u v w : Var? α} (u' : Var? α) (σ : u.Split v w) : Var? α
  := if u.used && σ.hasLeft then u' else u'.erase

def Var?.Split.wkRight {u v w : Var? α} (u' : Var? α) (σ : u.Split v w) : Var? α
  := if u.used && σ.hasRight then u' else u'.erase

@[simp]
theorem Var?.Split.wkLeft_neither {u' : Var? α} (A q) [hA : Var?.del ⟨A, q⟩]
  : (Split.neither hA).wkLeft u' = u'.erase := by simp [wkLeft]

@[simp]
theorem Var?.Split.wkLeft_left {u' : Var? α} (A q) :
  (Split.left A q).wkLeft u' = if 1 ≤ q then u' else u'.erase := by simp [wkLeft]

@[simp]
theorem Var?.Split.wkLeft_right {u' : Var? α} (A q) :
  (Split.right A q).wkLeft u' = u'.erase := by simp [wkLeft]

@[simp]
theorem Var?.Split.wkLeft_both {u' : Var? α} (u : Var? α) [hu : u.copy] :
  (Split.both hu).wkLeft u' = if u.used then u' else u'.erase := by simp [wkLeft]

@[simp]
theorem Var?.Split.wkRight_neither {u' : Var? α} (A q) [hA : Var?.del ⟨A, q⟩]
  : (Split.neither hA).wkRight u' = u'.erase := by simp [wkRight]

@[simp]
theorem Var?.Split.wkRight_left {u' : Var? α} (A q) :
  (Split.left A q).wkRight u' = u'.erase := by simp [wkRight]

@[simp]
theorem Var?.Split.wkRight_right {u' : Var? α} (A q) :
  (Split.right A q).wkRight u' = if 1 ≤ q then u' else u'.erase := by simp [wkRight]

@[simp]
theorem Var?.Split.wkRight_both {u' : Var? α} (u : Var? α) [hu : u.copy] :
  (Split.both hu).wkRight u' = if u.used then u' else u'.erase := by simp [wkRight]

@[simp]
theorem Var?.Split.wkLeft_unused {u' u v w : Var? α} (σ : u.Split v w) (hu : u.unused) :
  σ.wkLeft u' = u'.erase := by cases u; cases hu; rfl

@[simp]
theorem Var?.Split.wkRight_unused {u' u v w : Var? α} (σ : u.Split v w) (hu : u.unused) :
  σ.wkRight u' = u'.erase := by cases u; cases hu; rfl

@[simp]
theorem Var?.Split.wkLeft_used {u' u v w : Var? α} (σ : u.Split v w) (hu : u.used) :
  σ.wkLeft u' = if σ.hasLeft then u' else u'.erase := by rw [wkLeft]; simp [*]

@[simp]
instance Var?.Split.wkLeft_del {u' u v w : Var? α} [hv : v.del] (ρ : u' ≤ u) (σ : u.Split v w)
  : (σ.wkLeft u').del := by cases u with | mk A q => cases q using EQuant.casesZero with
  | zero => simp
  | rest => cases σ <;> simp [wkLeft] <;> apply Var?.del.anti ρ

@[simp]
instance Var?.Split.wkLeft_copy {u' u v w : Var? α} [hv : v.copy] (ρ : u' ≤ u) (σ : u.Split v w)
  : (σ.wkLeft u').copy := by cases u with | mk A q => cases q using EQuant.casesZero with
  | zero => simp
  | rest => cases σ <;> simp [wkLeft] <;> apply Var?.copy.anti ρ (by simp)

@[simp]
instance Var?.Split.wkRight_del {u' u v w : Var? α} [hw : w.del] (ρ : u' ≤ u) (σ : u.Split v w)
  : (σ.wkRight u').del := by cases u with | mk A q => cases q using EQuant.casesZero with
  | zero => simp
  | rest => cases σ <;> simp [wkRight] <;> apply Var?.del.anti ρ

@[simp]
instance Var?.Split.wkRight_copy {u' u v w : Var? α} [hw : w.copy] (ρ : u' ≤ u) (σ : u.Split v w)
  : (σ.wkRight u').copy := by cases u with | mk A q => cases q using EQuant.casesZero with
  | zero => simp
  | rest => cases σ <;> simp [wkRight] <;> apply Var?.copy.anti ρ (by simp)

def Var?.Split.wk {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.Split v w) :
  u'.Split (σ.wkLeft u') (σ.wkRight u') := match u with
  | ⟨A, 0⟩ => .neither (Var?.del.anti ρ)
  | ⟨A, (q : Quant)⟩ => match σ with
    | .neither h => .neither (Var?.del.anti ρ)
    | .left _ _ => .left _ _
    | .right _ _ => .right _ _
    | .both h => .both (Var?.copy.anti ρ (by simp))

@[simp]
def Var?.Split.comm {u v w : Var? α} : u.Split v w → u.Split w v
  | .neither h => .neither h
  | .left _ _ => .right _ _
  | .right _ _ => .left _ _
  | .both h => .both h

@[simp]
def Ctx?.Split.wkLeft {Γ' Γ Δ Ξ : Ctx? α} : Γ'.Wk Γ → Γ.Split Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkLeft ρ σ).cons v.erase
  | .cons (v := v) ρ _, .cons σ hlr => (wkLeft ρ σ).cons (hlr.wkLeft v)

@[simp]
def Ctx?.Split.wkRight {Γ' Γ Δ Ξ : Ctx? α} : Γ'.Wk Γ → Γ.Split Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkRight ρ σ).cons v.erase
  | .cons (v := v) ρ _, .cons σ hlr => (wkRight ρ σ).cons (hlr.wkRight v)

@[simp]
instance Ctx?.Split.wkLeft_del {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΔ : Δ.del]
  : (σ.wkLeft ρ).del := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΔ.head; have _ := hΔ.tail;
    simp [wkLeft, cons_del_iff, Var?.Split.wkLeft_del, *]
  | _ => simp [*]

@[simp]
instance Ctx?.Split.wkLeft_copy {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΔ : Δ.copy]
  : (σ.wkLeft ρ).copy := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΔ.head; have _ := hΔ.tail;
    simp [wkLeft, cons_copy_iff, Var?.Split.wkLeft_copy, *]
  | _ => simp [*]

@[simp]
instance Ctx?.Split.wkRight_del {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΞ : Ξ.del]
  : (σ.wkRight ρ).del := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΞ.head; have _ := hΞ.tail;
    simp [wkRight, cons_del_iff, Var?.Split.wkRight_del, *]
  | _ => simp [*]

@[simp]
instance Ctx?.Split.wkRight_copy {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΞ : Ξ.copy]
  : (σ.wkRight ρ).copy := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΞ.head; have _ := hΞ.tail;
    simp [wkRight, cons_copy_iff, Var?.Split.wkRight_copy, *]
  | _ => simp [*]

def Var?.Split.v12_3_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  : u₁₂₃.Split u₁₂ u₃ → u₁₂.Split u₁ u₂ → Var? α
  | .left A q, .left _ _ => ⟨A, 0⟩
  | _, _ => u₁₂₃
