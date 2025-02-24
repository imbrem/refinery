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

theorem Var?.Split.leftWk {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.Split v w) :
  σ.wkLeft u' ≤ v := by cases u' with | mk A q' => cases u with | mk _ q =>
    cases v; cases ρ.ty; cases σ <;> cases q using EQuant.casesZero <;> simp [ρ]

theorem Var?.Split.rightWk {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.Split v w) :
  σ.wkRight u' ≤ w := by cases u' with | mk A q' => cases u with | mk _ q =>
    cases w; cases ρ.ty; cases σ <;> cases q using EQuant.casesZero <;> simp [ρ]

@[simp]
def Var?.Split.comm {u v w : Var? α} : u.Split v w → u.Split w v
  | .neither h => .neither h
  | .left _ _ => .right _ _
  | .right _ _ => .left _ _
  | .both h => .both h

@[simp]
def Ctx?.Split.comm {Γ Δ Ξ : Ctx? α} : Γ.Split Δ Ξ → Γ.Split Ξ Δ
  | .nil => .nil
  | .cons h hvw => h.comm.cons hvw.comm

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

def Ctx?.Split.wk {Γ' Γ Δ Ξ : Ctx? α}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.Split Δ Ξ) → Γ'.Split (σ.wkLeft ρ) (σ.wkRight ρ)
  | .nil, .nil => .nil
  | .skip ρ hv, σ => .cons (σ.wk ρ) (.neither hv)
  | .cons (v := v) ρ hvw, .cons σ hlr => .cons (σ.wk ρ) (hlr.wk hvw)

@[simp]
def Ctx?.Split.leftWk {Γ' Γ Δ Ξ : Ctx? α} : (ρ : Γ'.Wk Γ) → (σ : Γ.Split Δ Ξ) → (σ.wkLeft ρ).Wk Δ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.leftWk ρ) inferInstance
  | .cons (v := v) ρ hvw, .cons σ hlr => .cons (σ.leftWk ρ) (hlr.leftWk hvw)

@[simp]
def Ctx?.Split.rightWk {Γ' Γ Δ Ξ : Ctx? α} : (ρ : Γ'.Wk Γ) → (σ : Γ.Split Δ Ξ) → (σ.wkRight ρ).Wk Ξ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.rightWk ρ) inferInstance
  | .cons (v := v) ρ hvw, .cons σ hlr => .cons (σ.rightWk ρ) (hlr.rightWk hvw)

@[simp]
theorem Ctx?.Split.ix_leftWk {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ)
  : (σ.leftWk ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.Split.leftWk_applied {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) (i : ℕ)
  : (σ.leftWk ρ) i = ρ i := by simp

@[simp]
theorem Ctx?.Split.ix_rightWk {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ)
  : (σ.rightWk ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.Split.rightWk_applied {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) (i : ℕ)
  : (σ.rightWk ρ) i = ρ i := by simp

@[simp]
def Var?.Split.leftCtx {u v w : Var? α} : u.Split v w → Ctx? α → Ctx? α
  | .left _ _, Γ | .both _, Γ => Γ
  | .right _ _, Γ | .neither _, Γ => Γ.erase

@[simp]
def Var?.Split.rightCtx {u v w : Var? α} : u.Split v w → Ctx? α → Ctx? α
  | .left _ _, Γ | .neither _, Γ => Γ.erase
  | .right _ _, Γ | .both _, Γ => Γ

def Var?.Split.v12_3_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α} : u₁₂₃.Split u₁₂ u₃ → u₁₂.Split u₁ u₂ → Var? α
  | .neither _, _ | .left _ _, .neither _ | .left _ _, .left _ _ => u₁₂₃.erase
  | _, _ => u₁₂₃

@[simp]
instance Var?.Split.v12_3_23_del {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  (h12_3 : u₁₂₃.Split u₁₂ u₃) (h12 : u₁₂.Split u₁ u₂) [h2 : u₂.del] [h3 : u₃.del]
  : (h12_3.v12_3_23 h12).del
  := by cases h12_3 <;> cases h12 <;> assumption

@[simp]
instance Var?.Split.v12_3_23_copy {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  (h12_3 : u₁₂₃.Split u₁₂ u₃) (h12 : u₁₂.Split u₁ u₂) [h2 : u₂.copy] [h3 : u₃.copy]
  : (h12_3.v12_3_23 h12).copy
  := by cases h12_3 <;> cases h12 <;> simp [v12_3_23, *]

def Var?.Split.s12_3_1_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  : (h12_3 : u₁₂₃.Split u₁₂ u₃) → (h12 : u₁₂.Split u₁ u₂) → u₁₂₃.Split u₁ (h12_3.v12_3_23 h12)
  | .neither h, .neither _
  | .neither h, .left _ _
  | .neither h, .right _ _
  | .neither h, .both _
  | .left _ _, .neither h => .neither h
  | .left _ _, .left _ _ => .left _ _
  | .left _ _, .right _ _ => .right _ _
  | .left _ _, .both h => .both h
  | .right _ _, .neither _
  | .right _ _, .left _ _
  | .right _ _, .right _ _
  | .right _ _, .both h => .right _ _
  | .both h, .neither _ => .right _ _
  | .both h, .left _ _ => .both h
  | .both _, .right _ _ => .right _ _
  | .both h, .both _ => .both h

def Var?.Split.s12_3_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  : (h12_3 : u₁₂₃.Split u₁₂ u₃) → (h12 : u₁₂.Split u₁ u₂) → (h12_3.v12_3_23 h12).Split u₂ u₃
  | .neither _, .neither _
  | .neither _, .left _ _
  | .neither _, .right _ _
  | .neither _, .both _
  | .left _ _, .neither h => .neither inferInstance
  | .left _ _, .left _ _ => .left _ _
  | .left _ _, .right _ _ => .left _ _
  | .left _ _, .both h => .left _ _
  | .right _ _, .neither _
  | .right _ _, .left _ _
  | .right _ _, .right _ _
  | .right _ _, .both h => .right _ _
  | .both _, .neither _ => .right _ _
  | .both _, .left _ _ => .right _ _
  | .both h, .right _ _ => .both h
  | .both h, .both _ => .both h

def Var?.Split.v1_23_12 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  : u₁₂₃.Split u₁ u₂₃ → u₂₃.Split u₂ u₃ → Var? α
  | .neither _, _ | .right _ _, .neither _ | .right _ _, .right _ _ => u₁₂₃.erase
  | _, _ => u₁₂₃

@[simp]
instance Var?.Split.v1_23_12_del {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  (h1_23 : u₁₂₃.Split u₁ u₂₃) (h23 : u₂₃.Split u₂ u₃) [h1 : u₁.del] [h2 : u₂.del]
  : (h1_23.v1_23_12 h23).del
  := by cases h1_23 <;> cases h23 <;> assumption

@[simp]
instance Var?.Split.v1_23_12_copy {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  (h1_23 : u₁₂₃.Split u₁ u₂₃) (h23 : u₂₃.Split u₂ u₃) [h1 : u₁.copy] [h2 : u₂.copy]
  : (h1_23.v1_23_12 h23).copy
  := by cases h1_23 <;> cases h23 <;> simp [v1_23_12, *]

def Var?.Split.s1_23_12_3 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  : (h1 : u₁₂₃.Split u₁ u₂₃) → (h23 : u₂₃.Split u₂ u₃) → u₁₂₃.Split (h1.v1_23_12 h23) u₃
  | .neither h, .neither _
  | .neither h, .left _ _
  | .neither h, .right _ _
  | .neither h, .both _
  | .right _ _, .neither h => .neither h
  | .left _ _ , .neither _
  | .left _ _, .left _ _
  | .left _ _, .right _ _
  | .left _ _, .both _ => .left _ _
  | .right _ _, .left _ _ => .left _ _
  | .right _ _, .right _ _ => .right _ _
  | .right _ _, .both h => .both h
  | .both _, .neither h => .left _ _
  | .both h, .left _ _ => .left _ _
  | .both h, .right _ _ => .both h
  | .both h, .both _ => .both h

def Var?.Split.s1_23_12 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  : (h1 : u₁₂₃.Split u₁ u₂₃) → (h23 : u₂₃.Split u₂ u₃) → (h1.v1_23_12 h23).Split u₁ u₂
  | .neither _, .neither _
  | .neither _, .left _ _
  | .neither _, .right _ _
  | .neither _, .both _
  | .right _ _, .neither _ => .neither inferInstance
  | .left _ _, .neither _ => .left _ _
  | .left _ _, .left _ _ => .left _ _
  | .left _ _, .right _ _ => .left _ _
  | .left _ _, .both _ => .left _ _
  | .right _ _, .left _ _ => .right _ _
  | .right _ _, .right _ _ => .right _ _
  | .right _ _, .both _ => .right _ _
  | .both _, .neither _ => .left _ _
  | .both h, .left _ _ => .both h
  | .both _, .right _ _ => .left _ _
  | .both h, .both _ => .both h

def Ctx?.Split.c1_23_12 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : Γ₁₂₃.Split Γ₁ Γ₂₃ → Γ₂₃.Split Γ₂ Γ₃ → Ctx? α
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (h.c1_23_12 h') (hvw.v1_23_12 hvw')

@[simp]
instance Ctx?.Split.c1_23_12_del {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) (h23 : Γ₂₃.Split Γ₂ Γ₃) [h1 : Γ₁.del] [h2 : Γ₂.del]
  : (h12_3.c1_23_12 h23).del
  := by
  generalize h1 = h1
  induction h12_3 generalizing Γ₂ Γ₃ <;> cases h23
  simp [c1_23_12]
  simp [c1_23_12, h2.head, h2.tail, h1.head, h1.tail, *]

@[simp]
instance Ctx?.Split.c1_23_12_copy {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) (h23 : Γ₂₃.Split Γ₂ Γ₃) [h1 : Γ₁.copy] [h2 : Γ₂.copy]
  : (h12_3.c1_23_12 h23).copy
  := by
  generalize h1 = h1
  induction h12_3 generalizing Γ₂ Γ₃ <;> cases h23
  simp [c1_23_12]
  simp [c1_23_12, h2.head, h2.tail, h1.head, h1.tail, *]

def Ctx?.Split.s1_23_12_3 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) → (h23 : Γ₂₃.Split Γ₂ Γ₃)
    → Γ₁₂₃.Split (h12_3.c1_23_12 h23) Γ₃
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s1_23_12_3 h h') (Var?.Split.s1_23_12_3 hvw hvw')

def Ctx?.Split.s1_23_12 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) → (h23 : Γ₂₃.Split Γ₂ Γ₃) → (h12_3.c1_23_12 h23).Split Γ₁ Γ₂
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s1_23_12 h h') (Var?.Split.s1_23_12 hvw hvw')

def Ctx?.Split.c12_3_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : Γ₁₂₃.Split Γ₁₂ Γ₃ → Γ₁₂.Split Γ₁ Γ₂ → Ctx? α
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (c12_3_23 h h') (Var?.Split.v12_3_23 hvw hvw')

@[simp]
instance Ctx?.Split.c12_3_23_del {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h2 : Γ₂.del] [h3 : Γ₃.del]
  : (h12_3.c12_3_23 h12).del
  := by
  generalize h3 = h3
  induction h12_3 generalizing Γ₁ Γ₂ <;> cases h12
  simp [c12_3_23]
  simp [c12_3_23, h2.head, h2.tail, h3.head, h3.tail, *]

@[simp]
instance Ctx?.Split.c12_3_23_copy {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h2 : Γ₂.copy] [h3 : Γ₃.copy]
  : (h12_3.c12_3_23 h12).copy
  := by
  generalize h3 = h3
  induction h12_3 generalizing Γ₁ Γ₂ <;> cases h12
  simp [c12_3_23]
  simp [c12_3_23, h2.head, h2.tail, h3.head, h3.tail, *]

def Ctx?.Split.s12_3_1_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) → (h12 : Γ₁₂.Split Γ₁ Γ₂)
    → Γ₁₂₃.Split Γ₁ (h12_3.c12_3_23 h12)
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s12_3_1_23 h h') (Var?.Split.s12_3_1_23 hvw hvw')

def Ctx?.Split.s12_3_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) → (h12 : Γ₁₂.Split Γ₁ Γ₂) → (h12_3.c12_3_23 h12).Split Γ₂ Γ₃
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s12_3_23 h h') (Var?.Split.s12_3_23 hvw hvw')

abbrev Ctx?.Split.c12_3_13 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
  : Ctx? α := h12_3.comm.c1_23_12 h12

theorem Ctx?.Split.c12_3_13_del {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h1 : Γ₁.del] [h3 : Γ₃.del]
  : (h12_3.c12_3_13 h12).del := inferInstance

theorem Ctx?.Split.c12_3_13_copy {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h1 : Γ₁.copy] [h3 : Γ₃.copy]
  : (h12_3.c12_3_13 h12).copy := inferInstance

abbrev Ctx?.Split.s12_3_13_2 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
  : Γ₁₂₃.Split (h12_3.c12_3_13 h12) Γ₂
  := h12_3.comm.s1_23_12_3 h12

abbrev Ctx?.Split.s12_3_31 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
  : (h12_3.c12_3_13 h12).Split Γ₃ Γ₁
  := h12_3.comm.s1_23_12 h12

abbrev Ctx?.Split.s12_3_13 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
  : (h12_3.c12_3_13 h12).Split Γ₁ Γ₃
  := (h12_3.s12_3_31 h12).comm

abbrev Ctx?.Split.c12_34_123 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : Ctx? α := h12_34.c1_23_12 h34

theorem Ctx?.Split.c12_34_123_del {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄) [h12 : Γ₁₂.del] [h3 : Γ₃.del]
  : (h12_34.c12_34_123 h34).del := inferInstance

theorem Ctx?.Split.c12_34_123_copy {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄) [h12 : Γ₁₂.copy] [h3 : Γ₃.copy]
  : (h12_34.c12_34_123 h34).copy := inferInstance

abbrev Ctx?.Split.s12_34_123_4 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : Γ₁₂₃₄.Split (h12_34.c12_34_123 h34) Γ₄ := h12_34.s1_23_12_3 h34

abbrev Ctx?.Split.s12_34_12_3 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : (h12_34.c12_34_123 h34).Split Γ₁₂ Γ₃ := h12_34.s1_23_12 h34

abbrev Ctx?.Split.c12_34_13 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : Ctx? α := (h12_34.s12_34_12_3 h34).c12_3_13 h12

theorem Ctx?.Split.c12_34_13_del {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  [h1 : Γ₁.del] [h3 : Γ₃.del]
  : (h12_34.c12_34_13 h12 h34).del := inferInstance

theorem Ctx?.Split.c12_34_13_copy {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  [h1 : Γ₁.copy] [h3 : Γ₃.copy]
  : (h12_34.c12_34_13 h12 h34).copy := inferInstance

abbrev Ctx?.Split.s12_34_13 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : (h12_34.c12_34_13 h12 h34).Split Γ₁ Γ₃ := (h12_34.s12_34_12_3 h34).s12_3_13 h12

abbrev Ctx?.Split.s12_34_13_2 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : (h12_34.c12_34_123 h34).Split (h12_34.c12_34_13 h12 h34) Γ₂
  := (h12_34.s12_34_12_3 h34).s12_3_13_2 h12

abbrev Ctx?.Split.c12_34_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : Ctx? α
  := (h12_34.s12_34_123_4 h34).c12_3_23 (h12_34.s12_34_13_2 h12 h34)

theorem Ctx?.Split.c12_34_24_del {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  [h2 : Γ₂.del] [h4 : Γ₄.del]
  : (h12_34.c12_34_24 h12 h34).del := inferInstance

theorem Ctx?.Split.c12_34_24_copy {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  [h2 : Γ₂.copy] [h4 : Γ₄.copy]
  : (h12_34.c12_34_24 h12 h34).copy := inferInstance

abbrev Ctx?.Split.s12_34_13_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : Γ₁₂₃₄.Split (h12_34.c12_34_13 h12 h34) (h12_34.c12_34_24 h12 h34)
  := (h12_34.s12_34_123_4 h34).s12_3_1_23 (h12_34.s12_34_13_2 h12 h34)

abbrev Ctx?.Split.s12_34_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
  : (h12_34.c12_34_24 h12 h34).Split Γ₂ Γ₄
  := (h12_34.s12_34_123_4 h34).s12_3_23 (h12_34.s12_34_13_2 h12 h34)
