import Refinery.Ctx.Basic

namespace Refinery

variable [HasQuant α]

inductive Var?.Split : Var? α → Var? α → Var? α → Type _
  | neither {A q} : del ⟨A, q⟩ → Split ⟨A, q⟩ ⟨A, 0⟩ ⟨A, 0⟩
  | left {v w} (h : v ≤ w) : Split v w v.erase
  | right {v w} (h : v ≤ w) : Split v v.erase w
  | sboth {u v w} (hu : u.scopy) (hv : u ≤ v) (hw : u ≤ w) : Split u v w

abbrev Var?.splitN (v : Var? α) [hv : v.del] : v.Split v.erase v.erase := .neither hv

abbrev Var?.splitL (v : Var? α) : v.Split v v.erase := .left (le_refl v)

abbrev Var?.splitR (v : Var? α) : v.Split v.erase v := .right (le_refl v)

-- abbrev Var?.splitB (v : Var? α) [hv : v.copy] : v.Split v v := .sboth hv (le_refl v) (le_refl v)

theorem Var?.Split.left_unused {u v w : Var? α} (σ : u.Split v w) (h : u.unused) : v.unused
  := by cases σ <;> (try simp [*]) <;> apply Var?.unused.mono <;> assumption

theorem Var?.Split.right_unused {u v w : Var? α} (σ : u.Split v w) (h : u.unused) : w.unused
  := by cases σ <;> (try simp [*]) <;> apply Var?.unused.mono <;> assumption

theorem Var?.Split.used_of_left {u v w : Var? α} (σ : u.Split v w) (h : v.used) : u.used
  := by cases σ
  <;> first | assumption | cases h | (apply Var?.used.anti (hw := by assumption); assumption)

theorem Var?.Split.used_of_right {u v w : Var? α} (σ : u.Split v w) (h : w.used) : u.used
  := by cases σ
  <;> first | assumption | cases h | (apply Var?.used.anti (hw := by assumption); assumption)

theorem Var?.Split.erase_eq_left {u v w : Var? α} (σ : u.Split v w)
  : u.erase = v.erase := by cases σ <;> simp [*]; rename_i h; rw [h.ty]; rename_i h _; rw [h.ty]

theorem Var?.Split.erase_eq_right {u v w : Var? α} (σ : u.Split v w)
  : u.erase = w.erase := by cases σ <;> simp [*]; rename_i h; rw [h.ty]; rename_i _ h; rw [h.ty]

theorem Var?.Split.erase_eq_both {u v w : Var? α} (σ : u.Split v w)
  : v.erase = w.erase := by rw [<-σ.erase_eq_left, <-σ.erase_eq_right]

theorem Var?.Split.wk_left_zero {u w : Var? α} (σ : u.Split ⟨X, 0⟩ w) : u.Wk w
  := by cases u; cases σ with
  | neither h => exact ⟨rfl, h.q, λ_ => h⟩
  | left h => cases h.ty; exact h
  | _ => assumption

theorem Var?.Split.wk_right_zero {u v : Var? α} (σ : u.Split v ⟨X, 0⟩) : u.Wk v
  := by cases u; cases σ with
  | neither h => exact ⟨rfl, h.q, λ_ => h⟩
  | right h => cases h.ty; exact h
  | _ => assumption

theorem Var?.Split.wk_left_both {u : Var? α} {X Y} {qX qY : Quant} (σ : u.Split ⟨X, qX⟩ ⟨Y, qY⟩)
  : u.Wk ⟨X, qX⟩ := by cases σ; assumption

theorem Var?.Split.wk_right_both {u : Var? α} {X Y} {qX qY : Quant} (σ : u.Split ⟨X, qX⟩ ⟨Y, qY⟩)
  : u.Wk ⟨Y, qY⟩ := by cases σ; assumption

theorem Var?.Split.scopy_both {u : Var? α} {X Y} {qX qY : Quant} (σ : u.Split ⟨X, qX⟩ ⟨Y, qY⟩)
  : u.scopy := by cases σ; assumption

theorem Var?.Split.ty_eq_left {u v w : Var? α} (σ : u.Split v w)
  : u.ty = v.ty := by cases σ <;> first | rfl | (apply Wk.ty; assumption)

theorem Var?.Split.ty_eq_right {u v w : Var? α} (σ : u.Split v w)
  : u.ty = w.ty := by cases σ <;> first | rfl | (apply Wk.ty; assumption)

theorem Var?.Split.ty_eq_out {u v w : Var? α} (σ : u.Split v w)
  : v.ty = w.ty := by rw [<-σ.ty_eq_left, <-σ.ty_eq_right]

@[simp]
theorem Var?.Split.zero_not_left_quant {X Y : Ty α} {q : Quant}
  (σ : Split ⟨X, 0⟩ ⟨Y, q⟩ v) : False
  := by cases σ with | left h | sboth _ h => exact Var?.Wk.not_zero_le h

@[simp]
theorem Var?.Split.zero_not_right_quant {X Y : Ty α} {q : Quant}
  (σ : Split ⟨X, 0⟩ v ⟨Y, q⟩) : False
  := by cases σ with | right h | sboth _ _ h => exact Var?.Wk.not_zero_le h

theorem Var?.Split.zero_left_quant {X Y : Ty α} {q}
  (σ : Split ⟨X, 0⟩ ⟨Y, q⟩ v) : q = 0
  := by cases q using EQuant.casesZero with
  | zero => rfl | rest => exact σ.zero_not_left_quant.elim

theorem Var?.Split.zero_right_quant {X Y : Ty α} {q}
  (σ : Split ⟨X, 0⟩ v ⟨Y, q⟩) : q = 0
  := by cases q using EQuant.casesZero with
  | zero => rfl | rest => exact σ.zero_not_right_quant.elim

theorem Var?.Split.del_in {u v w : Var? α} (σ : u.Split v w) [hu : v.del] [w.del] : u.del
  := by cases σ with
  | neither => assumption
  | left h | right h | sboth _ h => apply Var?.del.anti h

inductive Ctx?.Split : Ctx? α → Ctx? α → Ctx? α → Type _ where
  | nil : Ctx?.Split .nil .nil .nil
  | cons {Γ Δ Ξ v l r} (h : Split Γ Δ Ξ) (hvw : v.Split l r)
    : Split (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)

@[simp]
def Var?.Split.hasLeft {u v w : Var? α} : u.Split v w → Bool
  | .left _ => true | .sboth _ _ _ => true | _ => false

@[simp]
theorem Var?.Split.hasLeft_neither {A q} [hA : Var?.del ⟨A, q⟩]
  : (Split.neither (α := α) hA).hasLeft = false := rfl

@[simp]
theorem Var?.Split.hasLeft_left {v w : Var? α} (h : v ≤ w) : hasLeft (.left h) = true := rfl

@[simp]
theorem Var?.Split.hasLeft_right {v w : Var? α} (h : v ≤ w) : hasLeft (.right h) = false := rfl

@[simp]
theorem Var?.Split.hasLeft_sboth {u v w : Var? α} (hu : u.scopy) (hv : u ≤ v) (hw : u ≤ w)
  : hasLeft (.sboth hu hv hw) = true := rfl

def Var?.Split.hasRight {u v w : Var? α} : u.Split v w → Bool
  | .right _ => true | .sboth _ _ _ => true | _ => false

@[simp]
theorem Var?.Split.hasRight_neither {A q} [hA : Var?.del ⟨A, q⟩]
  : (Split.neither (α := α) hA).hasRight = false := rfl

@[simp]
theorem Var?.Split.hasRight_left {v w : Var? α} (h : v ≤ w) : hasRight (.left h) = false := rfl

@[simp]
theorem Var?.Split.hasRight_right {v w : Var? α} (h : v ≤ w) : hasRight (.right h) = true := rfl

@[simp]
theorem Var?.Split.hasRight_sboth {u v w : Var? α} (hu : u.scopy) (hv : u ≤ v) (hw : u ≤ w)
  : hasRight (.sboth hu hv hw) = true := rfl

def Var?.Split.cast {u v w u' v' w' : Var? α}
  (σ : u.Split v w) (hu : u = u') (hv : v = v') (hw : w = w')
  : u'.Split v' w'
  := hu ▸ hv ▸ hw ▸ σ

abbrev Var?.Split.cast_src {u v w u': Var? α}
  (σ : u.Split v w) (hu : u = u')
  : u'.Split v w
  := σ.cast hu rfl rfl

abbrev Var?.Split.cast_left {u v w v' : Var? α}
  (σ : u.Split v w) (hv : v = v')
  : u.Split v' w
  := σ.cast rfl hv rfl

abbrev Var?.Split.cast_right {u v w w' : Var? α}
  (σ : u.Split v w) (hw : w = w')
  : u.Split v w'
  := σ.cast rfl rfl hw

def Var?.Split.wk {u' u v w : Var? α} (ρ : u' ≤ u) : u.Split v w → u'.Split v w
  | .neither h => (Split.neither (h.anti ρ)).cast (by simp [ρ.ty]) (by rw [ρ.ty]) (by rw [ρ.ty])
  | .left h => (Split.left (le_trans ρ h)).cast_right ρ.erase_eq
  | .right h => (Split.right (le_trans ρ h)).cast_left ρ.erase_eq
  | .sboth hu hv hw => .sboth (hu.anti ρ) (le_trans ρ hv) (le_trans ρ hw)

@[simp]
def Var?.Split.comm {u v w : Var? α} : u.Split v w → u.Split w v
  | .neither h => .neither h
  | .left h => .right h
  | .right h => .left h
  | .sboth hu hv hw => .sboth hu hw hv

@[simp]
def Ctx?.Split.comm {Γ Δ Ξ : Ctx? α} : Γ.Split Δ Ξ → Γ.Split Ξ Δ
  | .nil => .nil
  | .cons h hvw => h.comm.cons hvw.comm

@[simp]
def Ctx?.Split.wkLeft {Γ' Γ Δ Ξ : Ctx? α} : Γ'.Wk Γ → Γ.Split Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkLeft ρ σ).cons v.erase
  | .cons (v := v) ρ _, .cons (l := l) σ hlr => (wkLeft ρ σ).cons l

@[simp]
def Ctx?.Split.wkRight {Γ' Γ Δ Ξ : Ctx? α} : Γ'.Wk Γ → Γ.Split Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkRight ρ σ).cons v.erase
  | .cons (v := v) ρ _, .cons (r := r) σ hlr => (wkRight ρ σ).cons r

@[simp]
instance Ctx?.Split.wkLeft_del {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΔ : Δ.del]
  : (σ.wkLeft ρ).del := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΔ.head; have _ := hΔ.tail;
    simp [wkLeft, cons_del_iff, *]
  | _ => simp [*]

@[simp]
instance Ctx?.Split.wkLeft_copy {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΔ : Δ.copy]
  : (σ.wkLeft ρ).copy := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΔ.head; have _ := hΔ.tail;
    simp [wkLeft, cons_copy_iff, *]
  | _ => simp [*]

@[simp]
instance Ctx?.Split.wkRight_del {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΞ : Ξ.del]
  : (σ.wkRight ρ).del := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΞ.head; have _ := hΞ.tail;
    simp [wkRight, cons_del_iff, *]
  | _ => simp [*]

@[simp]
instance Ctx?.Split.wkRight_copy {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.Split Δ Ξ) [hΞ : Ξ.copy]
  : (σ.wkRight ρ).copy := by
  induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; have _ := hΞ.head; have _ := hΞ.tail;
    simp [wkRight, cons_copy_iff, *]
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
  | .cons (v := v) ρ _, .cons σ hlr => .cons (σ.leftWk ρ) (le_refl _)

@[simp]
def Ctx?.Split.rightWk {Γ' Γ Δ Ξ : Ctx? α} : (ρ : Γ'.Wk Γ) → (σ : Γ.Split Δ Ξ) → (σ.wkRight ρ).Wk Ξ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.rightWk ρ) inferInstance
  | .cons (v := v) ρ _, .cons σ hlr => .cons (σ.rightWk ρ) (le_refl _)

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
  | .left _, Γ | .sboth _ _ _, Γ => Γ
  | .right _, Γ | .neither _, Γ => Γ.erase

@[simp]
def Var?.Split.rightCtx {u v w : Var? α} : u.Split v w → Ctx? α → Ctx? α
  | .left _, Γ | .neither _, Γ => Γ.erase
  | .right _, Γ | .sboth _ _ _, Γ => Γ

-- def Var?.Split.v12_3_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α} : u₁₂₃.Split u₁₂ u₃ → u₁₂.Split u₁ u₂ → Var? α
--   | .neither _, _ | .left _, .neither _ | .left _, .left _ => u₁₂₃.erase
--   | _, _ => u₁₂₃

-- @[simp]
-- instance Var?.Split.v12_3_23_del {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
--   (h12_3 : u₁₂₃.Split u₁₂ u₃) (h12 : u₁₂.Split u₁ u₂) [h2 : u₂.del] [h3 : u₃.del]
--   : (h12_3.v12_3_23 h12).del
--   := by cases h12_3 <;> cases h12 <;> simp [v12_3_23]

-- @[simp]
-- instance Var?.Split.v12_3_23_copy {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
--   (h12_3 : u₁₂₃.Split u₁₂ u₃) (h12 : u₁₂.Split u₁ u₂) [h2 : u₂.copy] [h3 : u₃.copy]
--   : (h12_3.v12_3_23 h12).copy
--   := by cases h12_3 <;> cases h12 <;> sorry

-- def Var?.Split.s12_3_1_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
--   : (h12_3 : u₁₂₃.Split u₁₂ u₃) → (h12 : u₁₂.Split u₁ u₂) → u₁₂₃.Split u₁ (h12_3.v12_3_23 h12)
--   | .neither h, .neither _ => sorry -- neither
--   | .neither h, .left hvw => sorry -- neither
--   | .neither h, .right _ => sorry -- neither
--   | .neither h, .sboth _ _ _ => sorry -- neither
--   | .left _, .neither h => sorry -- neither
--   | .left _, .left _ => sorry -- left
--   | .left _, .right _ => sorry -- right
--   | .left _, .sboth h _ _ => sorry -- both
--   | .right _, .neither _ => sorry -- right
--   | .right _, .left _ => sorry -- right
--   | .right _, .right _ => sorry -- right
--   | .right _, .sboth h _ _ => sorry -- right
--   | .sboth h _ _, .neither _ => sorry -- right
--   | .sboth h _ _, .left _ => sorry -- both
--   | .sboth _ _ _, .right _ => sorry -- right
--   | .sboth h _ _, .sboth _ _ _ => sorry -- both

-- def Var?.Split.s12_3_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
--   : (h12_3 : u₁₂₃.Split u₁₂ u₃) → (h12 : u₁₂.Split u₁ u₂) → (h12_3.v12_3_23 h12).Split u₂ u₃
--   | .neither _, .neither _ => sorry -- neither
--   | .neither _, .left _ => sorry -- neither
--   | .neither _, .right _ => sorry -- neither
--   | .neither _, .sboth _ _ _ => sorry -- neither
--   | .left _, .neither _ => sorry -- neither
--   | .left _, .left _ => sorry -- left
--   | .left _, .right _ => sorry -- left
--   | .left _, .sboth h _ _ => sorry -- left
--   | .right _, .neither _ => sorry -- right
--   | .right _, .left _ => sorry -- right
--   | .right _, .right _ => sorry -- right
--   | .right _, .sboth h _ _ => sorry -- right
--   | .sboth _ _ _, .neither _ => sorry -- right
--   | .sboth _ _ _, .left _ => sorry -- right
--   | .sboth h _ _, .right _ => sorry -- both
--   | .sboth h _ _, .sboth _ _ _ => sorry -- both

-- def Var?.Split.v1_23_12 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
--   : u₁₂₃.Split u₁ u₂₃ → u₂₃.Split u₂ u₃ → Var? α
--   | .neither _, _ | .right _, .neither _ | .right _, .right _ => u₁₂₃.erase
--   | _, _ => u₁₂₃

-- @[simp]
-- instance Var?.Split.v1_23_12_del {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
--   (h1_23 : u₁₂₃.Split u₁ u₂₃) (h23 : u₂₃.Split u₂ u₃) [h1 : u₁.del] [h2 : u₂.del]
--   : (h1_23.v1_23_12 h23).del
--   := by cases h1_23 <;> cases h23 <;> sorry

-- @[simp]
-- instance Var?.Split.v1_23_12_copy {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
--   (h1_23 : u₁₂₃.Split u₁ u₂₃) (h23 : u₂₃.Split u₂ u₃) [h1 : u₁.copy] [h2 : u₂.copy]
--   : (h1_23.v1_23_12 h23).copy
--   := by cases h1_23 <;> cases h23 <;> sorry

-- def Var?.Split.s1_23_12_3 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
--   : (h1 : u₁₂₃.Split u₁ u₂₃) → (h23 : u₂₃.Split u₂ u₃) → u₁₂₃.Split (h1.v1_23_12 h23) u₃
--   | .neither h, .neither _ => sorry -- neither
--   | .neither h, .left _ => sorry -- neither
--   | .neither h, .right _ => sorry -- neither
--   | .neither h, .sboth _ _ _ => sorry -- neither
--   | .right _, .neither h => sorry -- neither
--   | .left _ , .neither _ => sorry -- left
--   | .left _, .left _ => sorry -- left
--   | .left _, .right _ => sorry -- left
--   | .left _, .sboth _ _ _ => sorry -- left
--   | .right _, .left _ => sorry -- left
--   | .right _, .right _ => sorry -- right
--   | .right _, .sboth h _ _ => sorry -- both
--   | .sboth _ _ _, .neither h => sorry -- left
--   | .sboth h _ _, .left _ => sorry -- left
--   | .sboth h _ _, .right _ => sorry -- both
--   | .sboth h _ _, .sboth _ _ _ => sorry -- both

-- def Var?.Split.s1_23_12 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
--   : (h1 : u₁₂₃.Split u₁ u₂₃) → (h23 : u₂₃.Split u₂ u₃) → (h1.v1_23_12 h23).Split u₁ u₂
--   | .neither _, .neither _ => sorry -- neither
--   | .neither _, .left _  => sorry -- neither
--   | .neither _, .right _ => sorry -- neither
--   | .neither _, .sboth _ _ _ => sorry -- neither
--   | .right _, .neither _ => sorry -- neither
--   | .left _, .neither _ => sorry -- left
--   | .left _, .left _ => sorry -- left
--   | .left _, .right _ => sorry -- left
--   | .left _, .sboth _ _ _ => sorry -- left
--   | .right _, .left _ => sorry -- right
--   | .right _, .right _ => sorry -- right
--   | .right _, .sboth _ _ _ => sorry -- right
--   | .sboth _ _ _, .neither _ => sorry -- left
--   | .sboth h _ _, .left _ => sorry -- both
--   | .sboth _ _ _, .right _ => sorry -- left
--   | .sboth h _ _, .sboth _ _ _ => sorry -- both

-- def Ctx?.Split.c1_23_12 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   : Γ₁₂₃.Split Γ₁ Γ₂₃ → Γ₂₃.Split Γ₂ Γ₃ → Ctx? α
--   | .nil, .nil => .nil
--   | .cons h hvw, .cons h' hvw' => .cons (h.c1_23_12 h') (hvw.v1_23_12 hvw')

-- @[simp]
-- instance Ctx?.Split.c1_23_12_del {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) (h23 : Γ₂₃.Split Γ₂ Γ₃) [h1 : Γ₁.del] [h2 : Γ₂.del]
--   : (h12_3.c1_23_12 h23).del
--   := by
--   generalize h1 = h1
--   induction h12_3 generalizing Γ₂ Γ₃ <;> cases h23
--   simp [c1_23_12]
--   simp [c1_23_12, h2.head, h2.tail, h1.head, h1.tail, *]

-- @[simp]
-- instance Ctx?.Split.c1_23_12_copy {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) (h23 : Γ₂₃.Split Γ₂ Γ₃) [h1 : Γ₁.copy] [h2 : Γ₂.copy]
--   : (h12_3.c1_23_12 h23).copy
--   := by
--   generalize h1 = h1
--   induction h12_3 generalizing Γ₂ Γ₃ <;> cases h23
--   simp [c1_23_12]
--   simp [c1_23_12, h2.head, h2.tail, h1.head, h1.tail, *]

-- def Ctx?.Split.s1_23_12_3 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   : (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) → (h23 : Γ₂₃.Split Γ₂ Γ₃)
--     → Γ₁₂₃.Split (h12_3.c1_23_12 h23) Γ₃
--   | .nil, .nil => .nil
--   | .cons h hvw, .cons h' hvw' => .cons (s1_23_12_3 h h') (Var?.Split.s1_23_12_3 hvw hvw')

-- def Ctx?.Split.s1_23_12 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   : (h12_3 : Γ₁₂₃.Split Γ₁ Γ₂₃) → (h23 : Γ₂₃.Split Γ₂ Γ₃) → (h12_3.c1_23_12 h23).Split Γ₁ Γ₂
--   | .nil, .nil => .nil
--   | .cons h hvw, .cons h' hvw' => .cons (s1_23_12 h h') (Var?.Split.s1_23_12 hvw hvw')

-- def Ctx?.Split.c12_3_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   : Γ₁₂₃.Split Γ₁₂ Γ₃ → Γ₁₂.Split Γ₁ Γ₂ → Ctx? α
--   | .nil, .nil => .nil
--   | .cons h hvw, .cons h' hvw' => .cons (c12_3_23 h h') (Var?.Split.v12_3_23 hvw hvw')

-- @[simp]
-- instance Ctx?.Split.c12_3_23_del {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h2 : Γ₂.del] [h3 : Γ₃.del]
--   : (h12_3.c12_3_23 h12).del
--   := by
--   generalize h3 = h3
--   induction h12_3 generalizing Γ₁ Γ₂ <;> cases h12
--   simp [c12_3_23]
--   simp [c12_3_23, h2.head, h2.tail, h3.head, h3.tail, *]

-- @[simp]
-- instance Ctx?.Split.c12_3_23_copy {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h2 : Γ₂.copy] [h3 : Γ₃.copy]
--   : (h12_3.c12_3_23 h12).copy
--   := by
--   generalize h3 = h3
--   induction h12_3 generalizing Γ₁ Γ₂ <;> cases h12
--   simp [c12_3_23]
--   simp [c12_3_23, h2.head, h2.tail, h3.head, h3.tail, *]

-- def Ctx?.Split.s12_3_1_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   : (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) → (h12 : Γ₁₂.Split Γ₁ Γ₂)
--     → Γ₁₂₃.Split Γ₁ (h12_3.c12_3_23 h12)
--   | .nil, .nil => .nil
--   | .cons h hvw, .cons h' hvw' => .cons (s12_3_1_23 h h') (Var?.Split.s12_3_1_23 hvw hvw')

-- def Ctx?.Split.s12_3_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   : (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) → (h12 : Γ₁₂.Split Γ₁ Γ₂) → (h12_3.c12_3_23 h12).Split Γ₂ Γ₃
--   | .nil, .nil => .nil
--   | .cons h hvw, .cons h' hvw' => .cons (s12_3_23 h h') (Var?.Split.s12_3_23 hvw hvw')

-- abbrev Ctx?.Split.c12_3_13 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
--   : Ctx? α := h12_3.comm.c1_23_12 h12

-- theorem Ctx?.Split.c12_3_13_del {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h1 : Γ₁.del] [h3 : Γ₃.del]
--   : (h12_3.c12_3_13 h12).del := inferInstance

-- theorem Ctx?.Split.c12_3_13_copy {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂) [h1 : Γ₁.copy] [h3 : Γ₃.copy]
--   : (h12_3.c12_3_13 h12).copy := inferInstance

-- abbrev Ctx?.Split.s12_3_13_2 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
--   : Γ₁₂₃.Split (h12_3.c12_3_13 h12) Γ₂
--   := h12_3.comm.s1_23_12_3 h12

-- abbrev Ctx?.Split.s12_3_31 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
--   : (h12_3.c12_3_13 h12).Split Γ₃ Γ₁
--   := h12_3.comm.s1_23_12 h12

-- abbrev Ctx?.Split.s12_3_13 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
--   (h12_3 : Γ₁₂₃.Split Γ₁₂ Γ₃) (h12 : Γ₁₂.Split Γ₁ Γ₂)
--   : (h12_3.c12_3_13 h12).Split Γ₁ Γ₃
--   := (h12_3.s12_3_31 h12).comm

-- abbrev Ctx?.Split.c12_34_123 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : Ctx? α := h12_34.c1_23_12 h34

-- theorem Ctx?.Split.c12_34_123_del {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄) [h12 : Γ₁₂.del] [h3 : Γ₃.del]
--   : (h12_34.c12_34_123 h34).del := inferInstance

-- theorem Ctx?.Split.c12_34_123_copy {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄) [h12 : Γ₁₂.copy] [h3 : Γ₃.copy]
--   : (h12_34.c12_34_123 h34).copy := inferInstance

-- abbrev Ctx?.Split.s12_34_123_4 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : Γ₁₂₃₄.Split (h12_34.c12_34_123 h34) Γ₄ := h12_34.s1_23_12_3 h34

-- abbrev Ctx?.Split.s12_34_12_3 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : (h12_34.c12_34_123 h34).Split Γ₁₂ Γ₃ := h12_34.s1_23_12 h34

-- abbrev Ctx?.Split.c12_34_13 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : Ctx? α := (h12_34.s12_34_12_3 h34).c12_3_13 h12

-- theorem Ctx?.Split.c12_34_13_del {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   [h1 : Γ₁.del] [h3 : Γ₃.del]
--   : (h12_34.c12_34_13 h12 h34).del := inferInstance

-- theorem Ctx?.Split.c12_34_13_copy {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   [h1 : Γ₁.copy] [h3 : Γ₃.copy]
--   : (h12_34.c12_34_13 h12 h34).copy := inferInstance

-- abbrev Ctx?.Split.s12_34_13 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : (h12_34.c12_34_13 h12 h34).Split Γ₁ Γ₃ := (h12_34.s12_34_12_3 h34).s12_3_13 h12

-- abbrev Ctx?.Split.s12_34_13_2 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : (h12_34.c12_34_123 h34).Split (h12_34.c12_34_13 h12 h34) Γ₂
--   := (h12_34.s12_34_12_3 h34).s12_3_13_2 h12

-- abbrev Ctx?.Split.c12_34_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : Ctx? α
--   := (h12_34.s12_34_123_4 h34).c12_3_23 (h12_34.s12_34_13_2 h12 h34)

-- theorem Ctx?.Split.c12_34_24_del {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   [h2 : Γ₂.del] [h4 : Γ₄.del]
--   : (h12_34.c12_34_24 h12 h34).del := inferInstance

-- theorem Ctx?.Split.c12_34_24_copy {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   [h2 : Γ₂.copy] [h4 : Γ₄.copy]
--   : (h12_34.c12_34_24 h12 h34).copy := inferInstance

-- abbrev Ctx?.Split.s12_34_13_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : Γ₁₂₃₄.Split (h12_34.c12_34_13 h12 h34) (h12_34.c12_34_24 h12 h34)
--   := (h12_34.s12_34_123_4 h34).s12_3_1_23 (h12_34.s12_34_13_2 h12 h34)

-- abbrev Ctx?.Split.s12_34_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
--   (h12_34 : Γ₁₂₃₄.Split Γ₁₂ Γ₃₄) (h12 : Γ₁₂.Split Γ₁ Γ₂) (h34 : Γ₃₄.Split Γ₃ Γ₄)
--   : (h12_34.c12_34_24 h12 h34).Split Γ₂ Γ₄
--   := (h12_34.s12_34_123_4 h34).s12_3_23 (h12_34.s12_34_13_2 h12 h34)
