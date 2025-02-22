import Refinery.Ctx.Basic
import Refinery.Ctx.Split

namespace Refinery

variable [HasQuant α]

open HasQuant

inductive Var?.SSplit : Var? α → Var? α → Var? α → Type _
  | left (v) : SSplit v v v.erase
  | right (v) : SSplit v v.erase v
  | sboth {v} : v.scopy → SSplit v v v

theorem Var?.SSplit.left_unused {u v w : Var? α} (σ : u.SSplit v w) (h : u.unused) : v.unused
  := by cases σ <;> first | assumption | rfl

theorem Var?.SSplit.right_unused {u v w : Var? α} (σ : u.SSplit v w) (h : u.unused) : w.unused
  := by cases σ <;> first | rfl | assumption

theorem Var?.SSplit.used_of_left {u v w : Var? α} (σ : u.SSplit v w) (h : v.used) : u.used
  := by cases σ <;> first | assumption | cases h

theorem Var?.SSplit.used_of_right {u v w : Var? α} (σ : u.SSplit v w) (h : w.used) : u.used
  := by cases σ <;> first | cases h | assumption

theorem Var?.SSplit.erase_eq_left {u v w : Var? α} (h : u.SSplit v w)
  : u.erase = v.erase := by cases h <;> simp [*]

theorem Var?.SSplit.erase_eq_right {u v w : Var? α} (h : u.SSplit v w)
  : u.erase = w.erase := by cases h <;> simp [*]

theorem Var?.SSplit.erase_eq_both {u v w : Var? α} (h : u.SSplit v w)
  : v.erase = w.erase := by cases h <;> simp [*]

def Var?.SSplit.both (v : Var? α) [h : IsRel v] : SSplit v v v := if hv : v.used then
    SSplit.sboth hv.scopy
  else by
    rw [<-Var?.unused_iff] at hv
    convert SSplit.left v
    rw [hv.eq_erase]

def Var?.SSplit.wkLeft {u v w : Var? α} (u' : Var? α)
  : u.SSplit v w → Var? α
  | .left _ => if u.used then u' else u'.erase
  | .right _ => u'.erase
  | .sboth _ => if u.used then u' else u'.erase

@[simp]
theorem Var?.SSplit.wkLeft_left {u' u : Var? α}
  : (SSplit.left u).wkLeft u' = if u.used then u' else u'.erase := rfl

@[simp]
theorem Var?.SSplit.wkLeft_right {u' u : Var? α}
  : (SSplit.right u).wkLeft u' = u'.erase := rfl

@[simp]
theorem Var?.SSplit.wkLeft_sboth {u' u : Var? α} (h : u.scopy)
  : (SSplit.sboth h).wkLeft u' = if u.used then u' else u'.erase := rfl

def Var?.SSplit.wkRight {u v w : Var? α} (u' : Var? α)
  : u.SSplit v w → Var? α
  | .left _ => if u.used then u'.erase else u'
  | .right _ => u'
  | .sboth _ => u'

@[simp]
theorem Var?.SSplit.wkRight_left {u' u : Var? α}
  : (SSplit.left u).wkRight u' = if u.used then u'.erase else u' := rfl

@[simp]
theorem Var?.SSplit.wkRight_right {u' u : Var? α}
  : (SSplit.right u).wkRight u' = u' := rfl

@[simp]
theorem Var?.SSplit.wkRight_sboth {u' u : Var? α} (h : u.scopy)
  : (SSplit.sboth h).wkRight u' = u' := rfl

def Var?.SSplit.wkLeft' {u v w : Var? α} (u' : Var? α)
  : u.SSplit v w → Var? α
  | .left _ => u'
  | .right _ => if u.used then u'.erase else u'
  | .sboth _ => u'

@[simp]
theorem Var?.SSplit.wkLeft_left' {u' u : Var? α}
  : (SSplit.left u).wkLeft' u' = u' := rfl

@[simp]
theorem Var?.SSplit.wkLeft_right' {u' u : Var? α}
  : (SSplit.right u).wkLeft' u' = if u.used then u'.erase else u' := rfl

@[simp]
theorem Var?.SSplit.wkLeft_sboth' {u' u : Var? α} (h : u.scopy)
  : (SSplit.sboth h).wkLeft' u' = u' := rfl

def Var?.SSplit.wkRight' {u v w : Var? α} (u' : Var? α)
  : u.SSplit v w → Var? α
  | .left _ => u'.erase
  | .right _ => if u.used then u' else u'.erase
  | .sboth _ => if u.used then u' else u'.erase

@[simp]
theorem Var?.SSplit.wkRight_left' {u' u : Var? α}
  : (SSplit.left u).wkRight' u' = u'.erase := rfl

@[simp]
theorem Var?.SSplit.wkRight_right' {u' u : Var? α}
  : (SSplit.right u).wkRight' u' = if u.used then u' else u'.erase := rfl

@[simp]
theorem Var?.SSplit.wkRight_sboth' {u' u : Var? α} (h : u.scopy)
  : (SSplit.sboth h).wkRight' u' = if u.used then u' else u'.erase := rfl

theorem Var?.SSplit.left_ty_eq {u v w : Var? α} (h : u.SSplit v w) : u.ty = v.ty
  := by cases h <;> rfl

theorem Var?.SSplit.right_ty_eq {u v w : Var? α} (h : u.SSplit v w) : u.ty = w.ty
  := by cases h <;> rfl

theorem Var?.SSplit.left_eq_erase {u v w : Var? α} (h : u.SSplit v w) (hv : v.unused)
  : v = u.erase := by cases u; cases h <;> cases hv <;> rfl

theorem Var?.SSplit.right_eq_of_left {u v w : Var? α} (h : u.SSplit v w) (hv : v.unused)
  : w = u := by cases u; cases h <;> cases hv <;> rfl

theorem Var?.SSplit.right_eq_erase {u v w : Var? α} (h : u.SSplit v w) (hw : w.unused)
  : w = u.erase := by cases u; cases h <;> cases hw <;> rfl

theorem Var?.SSplit.left_eq {u v w : Var? α} (h : u.SSplit v w) (hv : v.used)
  : v = u := by cases h <;> first | rfl | cases hv

theorem Var?.SSplit.right_eq {u v w : Var? α} (h : u.SSplit v w) (hw : w.used)
  : w = u := by cases h <;> first | rfl | cases hw

theorem Var?.SSplit.scopy {u v w : Var? α}
  (h : u.SSplit v w) (hv : v.used) (hw : w.used) : u.scopy
  := by cases h <;> first | cases hv | cases hw | assumption

def Var?.SSplit.cast {u v w u' v' w' : Var? α}
  (h : u.SSplit v w) (hu : u = u') (hv : v = v') (hw : w = w')
  : u'.SSplit v' w' := hu ▸ hv ▸ hw ▸ h

def Var?.SSplit.choose {u v w : Var? α} (h : Nonempty (u.SSplit v w)) : u.SSplit v w
  := if hv : v.used then
      have ev := Eq.symm <| let ⟨h⟩ := h; h.left_eq hv;
      if hw : w.used then
        have ew := Eq.symm <| let ⟨h⟩ := h; h.right_eq hw;
        have hc := let ⟨h⟩ := h; h.scopy hv hw;
        (Var?.SSplit.sboth hc).cast rfl ev ew
      else
        have ew := Eq.symm <| let ⟨h⟩ := h; h.right_eq_erase (unused_iff.mpr hw);
        (Var?.SSplit.left u).cast rfl ev ew
    else
      have ev := Eq.symm <| let ⟨h⟩ := h; h.left_eq_erase (Var?.unused_iff.mpr hv);
      have ew := Eq.symm <| let ⟨h⟩ := h; h.right_eq_of_left (Var?.unused_iff.mpr hv);
      (Var?.SSplit.right u).cast rfl ev ew

inductive Ctx?.SSplit : Ctx? α → Ctx? α → Ctx? α → Type _ where
  | nil : Ctx?.SSplit .nil .nil .nil
  | cons {Γ Δ Ξ v l r} (h : SSplit Γ Δ Ξ) (hvw : v.SSplit l r)
    : SSplit (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)

def Ctx?.SSplit.choose {Γ Δ Ξ : Ctx? α} (h : Nonempty (Ctx?.SSplit Γ Δ Ξ)) : Ctx?.SSplit Γ Δ Ξ
  := match Γ, Δ, Ξ, h with
  | .nil, .nil, .nil, h => .nil
  | .nil, .cons _ _, _, h => False.elim (let ⟨h⟩ := h; by cases h)
  | .nil, _, .cons _ _, h => False.elim (let ⟨h⟩ := h; by cases h)
  | .cons _ _, .nil, _, h => False.elim (let ⟨h⟩ := h; by cases h)
  | .cons _ _, _, .nil, h => False.elim (let ⟨h⟩ := h; by cases h)
  | .cons Γ v, .cons Δ l, .cons Ξ r, h =>
    .cons (choose (let ⟨h⟩ := h; ⟨by cases h; assumption⟩))
          (Var?.SSplit.choose (let ⟨h⟩ := h; ⟨by cases h; assumption⟩))

theorem Ctx?.SSplit.left_length {Γ Δ Ξ : Ctx? α} (h : Ctx?.SSplit Γ Δ Ξ)
  : Ctx?.length Γ = Ctx?.length Δ
  := by induction h <;> simp [*]

theorem Ctx?.SSplit.right_length {Γ Δ Ξ : Ctx? α} (h : Ctx?.SSplit Γ Δ Ξ)
  : Ctx?.length Γ = Ctx?.length Ξ
  := by induction h <;> simp [*]

theorem Ctx?.SSplit.target_length {Γ Δ Ξ : Ctx? α} (h : Ctx?.SSplit Γ Δ Ξ)
  : Ctx?.length Δ = Ctx?.length Ξ := h.left_length.symm.trans h.right_length

def Ctx?.both (Γ : Ctx? α) [hΓ : Γ.copy] : Γ.SSplit Γ Γ := (λ_ => match Γ with
  | .nil => .nil
  | .cons Γ v => .cons (have _ := copy.tail Γ v; Γ.both) (have _ := copy.head Γ v; .both v)) hΓ

def Var?.SSplit.comm {u v w : Var? α} : u.SSplit v w → u.SSplit w v
  | .left _ => .right _
  | .right _ => .left _
  | .sboth h => .sboth h

def Var?.SSplit.v12_3_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  : u₁₂₃.SSplit u₁₂ u₃ → u₁₂.SSplit u₁ u₂ → Var? α
  | .left _, .left _ => u₁₂₃.erase
  | _, _ => u₁₂₃

def Var?.SSplit.s12_3_1_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  : (h12_3 : u₁₂₃.SSplit u₁₂ u₃) → (h12 : u₁₂.SSplit u₁ u₂) → u₁₂₃.SSplit u₁ (h12_3.v12_3_23 h12)
  | .left _, .left _ => .left _
  | .left _, .right _ => .right _
  | .left _, .sboth h => .sboth h
  | .right _, .left _ => .right _
  | .right _, .right _ => .right _
  | .right _, .sboth _ => .right _
  | .sboth h, .left _ => .sboth h
  | .sboth _, .right _ => .right _
  | .sboth h, .sboth _ => .sboth h

def Var?.SSplit.s12_3_23 {u₁₂₃ u₁₂ u₁ u₂ u₃ : Var? α}
  : (h12_3 : u₁₂₃.SSplit u₁₂ u₃) → (h12 : u₁₂.SSplit u₁ u₂) → (h12_3.v12_3_23 h12).SSplit u₂ u₃
  | .left _, .left _ => .left _
  | .left _, .right _ => .left _
  | .left _, .sboth _ => .left _
  | .right _, .left _ => .right _
  | .right _, .right _ => .right _
  | .right _, .sboth _ => .right _
  | .sboth _, .left _ => .right _
  | .sboth h, .right _ => .sboth h
  | .sboth h, .sboth _ => .sboth h

def Var?.SSplit.v1_23_12 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  : u₁₂₃.SSplit u₁ u₂₃ → u₂₃.SSplit u₂ u₃ → Var? α
  | .right _, .right _ => u₁₂₃.erase
  | _, _ => u₁₂₃

def Var?.SSplit.s1_23_12_3 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  : (h12_3 : u₁₂₃.SSplit u₁ u₂₃) → (h23 : u₂₃.SSplit u₂ u₃) → u₁₂₃.SSplit (h12_3.v1_23_12 h23) u₃
  | .left _, .left _ => .left _
  | .left _, .right _ => .left _
  | .left _, .sboth _ => .left _
  | .right _, .left _ => .left _
  | .right _, .right _ => .right _
  | .right _, .sboth h => .sboth h
  | .sboth _, .left _ => .left _
  | .sboth h, .right _ => .sboth h
  | .sboth h, .sboth _ => .sboth h

def Var?.SSplit.s1_23_12 {u₁₂₃ u₂₃ u₁ u₂ u₃ : Var? α}
  : (h12_3 : u₁₂₃.SSplit u₁ u₂₃) → (h23 : u₂₃.SSplit u₂ u₃) → (h12_3.v1_23_12 h23).SSplit u₁ u₂
  | .left _, .left _ => .left _
  | .left _, .right _ => .left _
  | .left _, .sboth h => .left _
  | .right _, .left _ => .right _
  | .right _, .right _ => .right _
  | .right _, .sboth _ => .right _
  | .sboth h, .left _ => .sboth h
  | .sboth h, .right _ => .left _
  | .sboth h, .sboth _ => .sboth h

def Ctx?.SSplit.comm {Γ Δ Ξ : Ctx? α} : Γ.SSplit Δ Ξ → Γ.SSplit Ξ Δ
  | .nil => .nil
  | .cons h hvw => .cons (SSplit.comm h) hvw.comm

def Ctx?.SSplit.c1_23_12 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : Γ₁₂₃.SSplit Γ₁ Γ₂₃ → Γ₂₃.SSplit Γ₂ Γ₃ → Ctx? α
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (c1_23_12 h h') (Var?.SSplit.v1_23_12 hvw hvw')

def Ctx?.SSplit.s1_23_12_3 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.SSplit Γ₁ Γ₂₃) → (h23 : Γ₂₃.SSplit Γ₂ Γ₃)
    → Γ₁₂₃.SSplit (h12_3.c1_23_12 h23) Γ₃
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s1_23_12_3 h h') (Var?.SSplit.s1_23_12_3 hvw hvw')

def Ctx?.SSplit.s1_23_12 {Γ₁₂₃ Γ₂₃ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.SSplit Γ₁ Γ₂₃) → (h23 : Γ₂₃.SSplit Γ₂ Γ₃) → (h12_3.c1_23_12 h23).SSplit Γ₁ Γ₂
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s1_23_12 h h') (Var?.SSplit.s1_23_12 hvw hvw')

def Ctx?.SSplit.c12_3_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : Γ₁₂₃.SSplit Γ₁₂ Γ₃ → Γ₁₂.SSplit Γ₁ Γ₂ → Ctx? α
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (c12_3_23 h h') (Var?.SSplit.v12_3_23 hvw hvw')

def Ctx?.SSplit.s12_3_1_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) → (h12 : Γ₁₂.SSplit Γ₁ Γ₂)
    → Γ₁₂₃.SSplit Γ₁ (h12_3.c12_3_23 h12)
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s12_3_1_23 h h') (Var?.SSplit.s12_3_1_23 hvw hvw')

def Ctx?.SSplit.s12_3_23 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  : (h12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) → (h12 : Γ₁₂.SSplit Γ₁ Γ₂) → (h12_3.c12_3_23 h12).SSplit Γ₂ Γ₃
  | .nil, .nil => .nil
  | .cons h hvw, .cons h' hvw' => .cons (s12_3_23 h h') (Var?.SSplit.s12_3_23 hvw hvw')

theorem Ctx?.SSplit.erase_eq_left {Γ Δ Ξ : Ctx? α} (h : Γ.SSplit Δ Ξ)
  : Γ.erase = Δ.erase := by induction h with
  | nil => rfl
  | cons h hvw I => simp [I, hvw.erase_eq_left]

theorem Ctx?.SSplit.erase_eq_right {Γ Δ Ξ : Ctx? α} (h : Γ.SSplit Δ Ξ)
  : Γ.erase = Ξ.erase := h.comm.erase_eq_left

theorem Ctx?.SSplit.erase_eq {Γ Δ Ξ : Ctx? α} (h : Γ.SSplit Δ Ξ)
  : Δ.erase = Ξ.erase := h.erase_eq_left.symm.trans h.erase_eq_right

def Ctx?.SSplit.cast {Γ Δ Ξ Γ' Δ' Ξ' : Ctx? α}
  (h : Γ.SSplit Δ Ξ) (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hΞ : Ξ = Ξ')
  : Γ'.SSplit Δ' Ξ' := hΓ ▸ hΔ ▸ hΞ ▸ h

abbrev Ctx?.SSplit.cast_src {Γ Δ Ξ Γ' : Ctx? α}
  (h : Γ.SSplit Δ Ξ) (hΓ : Γ = Γ')
  : Γ'.SSplit Δ Ξ := h.cast hΓ rfl rfl

abbrev Ctx?.SSplit.cast_left {Γ Δ Ξ Δ' : Ctx? α}
  (h : Γ.SSplit Δ Ξ) (hΔ : Δ = Δ')
  : Γ.SSplit Δ' Ξ := h.cast rfl hΔ rfl

abbrev Ctx?.SSplit.cast_right {Γ Δ Ξ Ξ' : Ctx? α}
  (h : Γ.SSplit Δ Ξ) (hΞ : Ξ = Ξ')
  : Γ.SSplit Δ Ξ' := h.cast rfl rfl hΞ

abbrev Ctx?.SSplit.c12_3_13 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) (h12 : Γ₁₂.SSplit Γ₁ Γ₂)
  : Ctx? α := h12_3.comm.c1_23_12 h12

abbrev Ctx?.SSplit.s12_3_13_2 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) (h12 : Γ₁₂.SSplit Γ₁ Γ₂)
  : Γ₁₂₃.SSplit (h12_3.c12_3_13 h12) Γ₂
  := h12_3.comm.s1_23_12_3 h12

abbrev Ctx?.SSplit.s12_3_31 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) (h12 : Γ₁₂.SSplit Γ₁ Γ₂)
  : (h12_3.c12_3_13 h12).SSplit Γ₃ Γ₁
  := h12_3.comm.s1_23_12 h12

abbrev Ctx?.SSplit.s12_3_13 {Γ₁₂₃ Γ₁₂ Γ₁ Γ₂ Γ₃ : Ctx? α}
  (h12_3 : Γ₁₂₃.SSplit Γ₁₂ Γ₃) (h12 : Γ₁₂.SSplit Γ₁ Γ₂)
  : (h12_3.c12_3_13 h12).SSplit Γ₁ Γ₃
  := (h12_3.s12_3_31 h12).comm

abbrev Ctx?.SSplit.c12_34_123 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : Ctx? α := h12_34.c1_23_12 h34

abbrev Ctx?.SSplit.s12_34_123_4 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : Γ₁₂₃₄.SSplit (h12_34.c12_34_123 h34) Γ₄ := h12_34.s1_23_12_3 h34

abbrev Ctx?.SSplit.s12_34_12_3 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : (h12_34.c12_34_123 h34).SSplit Γ₁₂ Γ₃ := h12_34.s1_23_12 h34

abbrev Ctx?.SSplit.c12_34_13 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h12 : Γ₁₂.SSplit Γ₁ Γ₂) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : Ctx? α := (h12_34.s12_34_12_3 h34).c12_3_13 h12

abbrev Ctx?.SSplit.s12_34_13 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h12 : Γ₁₂.SSplit Γ₁ Γ₂) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : (h12_34.c12_34_13 h12 h34).SSplit Γ₁ Γ₃ := (h12_34.s12_34_12_3 h34).s12_3_13 h12

abbrev Ctx?.SSplit.s12_34_13_2 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h12 : Γ₁₂.SSplit Γ₁ Γ₂) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : (h12_34.c12_34_123 h34).SSplit (h12_34.c12_34_13 h12 h34) Γ₂
  := (h12_34.s12_34_12_3 h34).s12_3_13_2 h12

abbrev Ctx?.SSplit.c12_34_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h12 : Γ₁₂.SSplit Γ₁ Γ₂) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : Ctx? α
  := (h12_34.s12_34_123_4 h34).c12_3_23 (h12_34.s12_34_13_2 h12 h34)

abbrev Ctx?.SSplit.s12_34_13_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h12 : Γ₁₂.SSplit Γ₁ Γ₂) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : Γ₁₂₃₄.SSplit (h12_34.c12_34_13 h12 h34) (h12_34.c12_34_24 h12 h34)
  := (h12_34.s12_34_123_4 h34).s12_3_1_23 (h12_34.s12_34_13_2 h12 h34)

abbrev Ctx?.SSplit.s12_34_24 {Γ₁₂₃₄ Γ₁₂ Γ₃₄ Γ₃ Γ₄ : Ctx? α}
  (h12_34 : Γ₁₂₃₄.SSplit Γ₁₂ Γ₃₄) (h12 : Γ₁₂.SSplit Γ₁ Γ₂) (h34 : Γ₃₄.SSplit Γ₃ Γ₄)
  : (h12_34.c12_34_24 h12 h34).SSplit Γ₂ Γ₄
  := (h12_34.s12_34_123_4 h34).s12_3_23 (h12_34.s12_34_13_2 h12 h34)

def Var?.SSplit.toSplit {u v w : Var? α} (h : u.SSplit v w) : u.Split v w := match h with
  | Var?.SSplit.left _ => Var?.Split.left (le_refl _)
  | Var?.SSplit.right _ => Var?.Split.right (le_refl _)
  | Var?.SSplit.sboth hu => Var?.Split.sboth hu (le_refl _) (le_refl _)

def Ctx?.SSplit.toSplit {Γ Δ Ξ : Ctx? α} : Ctx?.SSplit Γ Δ Ξ → Ctx?.Split Γ Δ Ξ
  | .nil => .nil
  | .cons h hvw => .cons h.toSplit hvw.toSplit

def Var?.SSplit.wk {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w) :
  u'.SSplit (σ.wkLeft u') (σ.wkRight u') := match u, σ with
  | ⟨A, (q : Quant)⟩, .left _ => .left _
  | ⟨A, (q : Quant)⟩, .right _ => .right _
  | ⟨A, 0⟩, .left _ | ⟨A, 0⟩, .right _ => .right _
  | ⟨A, (q : Quant)⟩, .sboth h => .sboth (h.anti ρ)

@[simp]
theorem Var?.SSplit.wk_left_quant {u' : Var? α} {A : Ty α} {q : Quant}
  (ρ : u' ≤ ⟨A, q⟩) : (SSplit.left ⟨A, q⟩).wk ρ = .left u' := rfl

@[simp]
theorem Var?.SSplit.wk_right_quant {u' : Var? α} {A : Ty α} {q : Quant}
  (ρ : u' ≤ ⟨A, q⟩) : (SSplit.right ⟨A, q⟩).wk ρ = .right u' := rfl

@[simp]
theorem Var?.SSplit.wk_left_zero {u' : Var? α} {A : Ty α}
  (ρ : u' ≤ ⟨A, 0⟩) : (SSplit.left ⟨A, 0⟩).wk ρ = .right u' := rfl

@[simp]
theorem Var?.SSplit.wk_right_zero {u' : Var? α} {A : Ty α}
  (ρ : u' ≤ ⟨A, 0⟩) : (SSplit.right ⟨A, 0⟩).wk ρ = .right u' := rfl

@[simp]
theorem Var?.SSplit.wk_sboth_quant {u' : Var? α} {A : Ty α} {q : Quant}
  (ρ : u' ≤ ⟨A, q⟩) (h : (Var?.mk A q).scopy)
  : (SSplit.sboth h).wk ρ = SSplit.sboth (h.anti ρ) := rfl

@[simp]
theorem Var?.SSplit.leftWk {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : (σ.wkLeft u') ≤ v := by cases u with | mk A q =>
    cases q using EQuant.casesZero <;> cases σ <;> first | exact ρ | exact (erase_mono ρ)

@[simp]
theorem Var?.SSplit.rightWk {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : (σ.wkRight u') ≤ w := by cases u with | mk A q =>
    cases q using EQuant.casesZero <;> cases σ <;> first | exact ρ | exact (erase_mono ρ)

def Var?.SSplit.wk' {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w) :
  u'.SSplit (σ.wkLeft' u') (σ.wkRight' u') := match u, σ with
  | ⟨A, (q : Quant)⟩, .left _ => .left _
  | ⟨A, (q : Quant)⟩, .right _ => .right _
  | ⟨A, 0⟩, .left _ | ⟨A, 0⟩, .right _ => .left _
  | ⟨A, (q : Quant)⟩, .sboth h => .sboth (h.anti ρ)

@[simp]
theorem Var?.SSplit.wk_left_quant' {u' : Var? α} {A : Ty α} {q : Quant}
  (ρ : u' ≤ ⟨A, q⟩) : (SSplit.left ⟨A, q⟩).wk' ρ = .left u' := rfl

@[simp]
theorem Var?.SSplit.wk_right_quant' {u' : Var? α} {A : Ty α} {q : Quant}
  (ρ : u' ≤ ⟨A, q⟩) : (SSplit.right ⟨A, q⟩).wk' ρ = .right u' := rfl

@[simp]
theorem Var?.SSplit.wk_left_zero' {u' : Var? α} {A : Ty α}
  (ρ : u' ≤ ⟨A, 0⟩) : (SSplit.left ⟨A, 0⟩).wk' ρ = .left u' := rfl

@[simp]
theorem Var?.SSplit.wk_right_zero' {u' : Var? α} {A : Ty α}
  (ρ : u' ≤ ⟨A, 0⟩) : (SSplit.right ⟨A, 0⟩).wk' ρ = .left u' := rfl

@[simp]
theorem Var?.SSplit.wk_sboth_quant' {u' : Var? α} {A : Ty α} {q : Quant}
  (ρ : u' ≤ ⟨A, q⟩) (h : (Var?.mk A q).scopy)
  : (SSplit.sboth h).wk' ρ = SSplit.sboth (h.anti ρ) := rfl

@[simp]
theorem Var?.SSplit.leftWk' {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : (σ.wkLeft' u') ≤ v := by cases u with | mk A q =>
    cases q using EQuant.casesZero <;> cases σ <;> first | exact ρ | exact (erase_mono ρ)

@[simp]
theorem Var?.SSplit.rightWk' {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : (σ.wkRight' u') ≤ w := by cases u with | mk A q =>
    cases q using EQuant.casesZero <;> cases σ <;> first | exact ρ | exact (erase_mono ρ)

@[simp]
def Ctx?.SSplit.wkLeft {Γ' Γ Δ Ξ : Ctx? α}
  : Γ'.Wk Γ → Γ.SSplit Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkLeft ρ σ).cons v.erase
  | .cons (v := v) ρ _, .cons σ hlr => (wkLeft ρ σ).cons (hlr.wkLeft v)

@[simp]
def Ctx?.SSplit.wkRight {Γ' Γ Δ Ξ : Ctx? α}
  : Γ'.Wk Γ → Γ.SSplit Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkRight ρ σ).cons v
  | .cons (v := v) ρ _, .cons σ hlr => (wkRight ρ σ).cons (hlr.wkRight v)

@[simp]
def Ctx?.SSplit.leftWk {Γ' Γ Δ Ξ : Ctx? α}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.SSplit Δ Ξ) → (σ.wkLeft ρ).Wk Δ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.leftWk ρ) inferInstance
  | .cons ρ hvw, .cons σ hlr => .cons (σ.leftWk ρ) (hlr.leftWk hvw)

@[simp]
def Ctx?.SSplit.rightWk {Γ' Γ Δ Ξ : Ctx? α}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.SSplit Δ Ξ) → (σ.wkRight ρ).Wk Ξ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.rightWk ρ) inferInstance
  | .cons ρ hvw, .cons σ hlr => .cons (σ.rightWk ρ) (hlr.rightWk hvw)

@[simp]
theorem Ctx?.SSplit.ix_leftWk {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : (σ.leftWk ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.SSplit.leftWk_applied {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) (i : ℕ)
  : (σ.leftWk ρ) i = ρ i := by simp

@[simp]
theorem Ctx?.SSplit.ix_rightWk {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : (σ.rightWk ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.SSplit.rightWk_applied {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) (i : ℕ)
  : (σ.rightWk ρ) i = ρ i := by simp

@[simp]
def Ctx?.SSplit.wk {Γ' Γ Δ Ξ : Ctx? α}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.SSplit Δ Ξ) → Γ'.SSplit (σ.wkLeft ρ) (σ.wkRight ρ)
  | .nil, .nil => .nil
  | .skip (v := ⟨A, q⟩) ρ _, σ => .cons (σ.wk ρ) (.right ..)
  | .cons ρ hvw, .cons σ hlr => .cons (σ.wk ρ) (hlr.wk hvw)

theorem Var?.SSplit.wkLeft_copy
  {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w) [hv : v.copy]
  : (σ.wkLeft u').copy := by cases u with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases σ <;> simp
    | rest q => cases σ <;> simp <;> apply copy.anti (hw := _) ρ <;> simp [*]

theorem Var?.SSplit.wkLeft_del
  {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w) [hv : v.del]
  : (σ.wkLeft u').del := by cases u with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases σ <;> simp
    | rest q => cases σ <;> simp <;> apply del.anti (hw := _) ρ <;> simp [*]

instance Ctx?.SSplit.wkLeft_del
  {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) [hΔ : Δ.del] : (σ.wkLeft ρ).del
  := by induction ρ generalizing Δ Ξ with
  | nil => simp
  | skip ρ hv I => simp [*]
  | cons ρ hvw I =>
    cases σ; have _ := hΔ.head; have _ := hΔ.tail;
    simp [wkLeft, cons_del_iff, Var?.SSplit.wkLeft_del, *]

-- Since all unused variables go on the right, we have the following useful theorems:
instance Ctx?.SSplit.wkLeft_copy
  {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) [hΔ : Δ.copy] : (σ.wkLeft ρ).copy
  := by induction ρ generalizing Δ Ξ with
  | nil => simp
  | skip ρ hv I => simp [*]
  | cons ρ hvw I =>
    cases σ; have _ := hΔ.head; have _ := hΔ.tail;
    simp [wkLeft, cons_copy_iff, Var?.SSplit.wkLeft_copy, *]

@[simp]
def Ctx?.SSplit.wkLeft' {Γ' Γ Δ Ξ : Ctx? α}
  : Γ'.Wk Γ → Γ.SSplit Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkLeft' ρ σ).cons v
  | .cons (v := v) ρ _, .cons σ hlr => (wkLeft' ρ σ).cons (hlr.wkLeft' v)

@[simp]
def Ctx?.SSplit.wkRight' {Γ' Γ Δ Ξ : Ctx? α}
  : Γ'.Wk Γ → Γ.SSplit Δ Ξ → Ctx? α
  | .nil, _ => .nil
  | .skip (v := v) ρ _, σ => (wkRight' ρ σ).cons v.erase
  | .cons (v := v) ρ _, .cons σ hlr => (wkRight' ρ σ).cons (hlr.wkRight' v)

@[simp]
def Ctx?.SSplit.leftWk' {Γ' Γ Δ Ξ : Ctx? α}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.SSplit Δ Ξ) → (σ.wkLeft' ρ).Wk Δ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.leftWk' ρ) inferInstance
  | .cons ρ hvw, .cons σ hlr => .cons (σ.leftWk' ρ) (hlr.leftWk' hvw)

@[simp]
def Ctx?.SSplit.rightWk' {Γ' Γ Δ Ξ : Ctx? α}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.SSplit Δ Ξ) → (σ.wkRight' ρ).Wk Ξ
  | .nil, .nil => .nil
  | .skip ρ _, σ => .skip (σ.rightWk' ρ) inferInstance
  | .cons ρ hvw, .cons σ hlr => .cons (σ.rightWk' ρ) (hlr.rightWk' hvw)

@[simp]
theorem Ctx?.SSplit.ix_leftWk' {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : (σ.leftWk' ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.SSplit.leftWk_applied' {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) (i : ℕ)
  : (σ.leftWk ρ) i = ρ i := by simp

@[simp]
theorem Ctx?.SSplit.ix_rightWk' {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : (σ.rightWk ρ).ix = ρ := by
    induction ρ generalizing Δ Ξ <;> cases σ <;> simp [*]

theorem Ctx?.SSplit.rightWk_applied' {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) (i : ℕ)
  : (σ.rightWk ρ) i = ρ i := by simp

@[simp]
def Ctx?.SSplit.wk' {Γ' Γ Δ Ξ : Ctx? α}
  : (ρ : Γ'.Wk Γ) → (σ : Γ.SSplit Δ Ξ) → Γ'.SSplit (σ.wkLeft' ρ) (σ.wkRight' ρ)
  | .nil, .nil => .nil
  | .skip (v := ⟨A, q⟩) ρ _, σ => .cons (σ.wk' ρ) (.left ..)
  | .cons ρ hvw, .cons σ hlr => .cons (σ.wk' ρ) (hlr.wk' hvw)

theorem Var?.SSplit.wkRight_copy'
  {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w) [hw : w.copy]
  : (σ.wkRight' u').copy := by cases u with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases σ <;> simp
    | rest q => cases σ <;> simp <;> apply copy.anti (hw := _) ρ <;> simp [*]

theorem Var?.SSplit.wkLeft_del'
  {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w) [hv : v.del]
  : (σ.wkLeft u').del := by cases u with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases σ <;> simp
    | rest q => cases σ <;> simp <;> apply del.anti (hw := _) ρ <;> simp [*]

instance Ctx?.SSplit.wkLeft_del'
  {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) [hΔ : Δ.del] : (σ.wkLeft ρ).del
  := by induction ρ generalizing Δ Ξ with
  | nil => simp
  | skip ρ hv I => simp [*]
  | cons ρ hvw I =>
    cases σ; have _ := hΔ.head; have _ := hΔ.tail;
    simp [wkLeft, cons_del_iff, Var?.SSplit.wkLeft_del, *]

-- Since all unused variables go on the left, we have the following useful theorem:
instance Ctx?.SSplit.wkRight_copy'
  {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ) [hΞ : Ξ.copy] : (σ.wkRight' ρ).copy
  := by induction ρ generalizing Δ Ξ with
  | nil => simp
  | skip ρ hv I => simp[*]
  | cons ρ hvw I =>
    cases σ; have _ := hΞ.head; have _ := hΞ.tail;
    simp [wkLeft, cons_copy_iff, Var?.SSplit.wkRight_copy', *]

def Ctx?.erase_right : (Γ : Ctx? α) → Γ.SSplit Γ Γ.erase
  | .nil => .nil
  | .cons Γ v => .cons Γ.erase_right (.left v)

def Ctx?.erase_left : (Γ : Ctx? α) → Γ.SSplit Γ.erase Γ
  | .nil => .nil
  | .cons Γ v => .cons Γ.erase_left (.right v)

theorem Var?.SSplit.wkLeft_quant
  {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : quant v ≤ quant (σ.wkLeft u') := by cases u with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases σ <;> rfl
    | rest q =>
      cases σ <;> simp <;>
      cases u' with | mk A' q' =>
      cases q' using EQuant.casesZero with
      | zero => cases ρ.q using EQuant.le.casesLE
      | rest q' =>
        have h := ρ.q; simp only [quant] at h;
        cases ρ.ty; simp [quant]; apply inf_le_of_left_le; rw [<-EQuant.coe_le_coe]; exact ρ.q

theorem Var?.SSplit.wkRight_quant'
  {u' u v w : Var? α} (ρ : u' ≤ u) (σ : u.SSplit v w)
  : quant w ≤ quant (σ.wkRight' u') := by cases u with | mk A q =>
    cases q using EQuant.casesZero with
    | zero => cases σ <;> rfl
    | rest q =>
      cases σ <;> simp <;>
      cases u' with | mk A' q' =>
      cases q' using EQuant.casesZero with
      | zero => cases ρ.q using EQuant.le.casesLE
      | rest q' =>
        have h := ρ.q; simp only [quant] at h;
        cases ρ.ty; simp [quant]; apply inf_le_of_left_le; rw [<-EQuant.coe_le_coe]; exact ρ.q

theorem Ctx?.SSplit.wkLeft_quant
  {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : quant Δ ≤ quant (σ.wkLeft ρ) := by induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; simp only [quant_cons, wkLeft]
    apply inf_le_inf
    apply_assumption
    apply Var?.SSplit.wkLeft_quant
    assumption
  | _ => simp [*]

theorem Ctx?.SSplit.wkRight_quant'
  {Γ' Γ Δ Ξ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : Γ.SSplit Δ Ξ)
  : quant Ξ ≤ quant (σ.wkRight' ρ) := by induction ρ generalizing Δ Ξ with
  | cons =>
    cases σ; simp only [quant_cons, wkRight']
    apply inf_le_inf
    apply_assumption
    apply Var?.SSplit.wkRight_quant'
    assumption
  | _ => simp [*]

@[simp]
def Var?.SSplit.leftCtx {u v w : Var? α} : u.SSplit v w → Ctx? α → Ctx? α
  | .left _, Γ | .sboth _, Γ => Γ
  | .right _, Γ => Γ.erase

@[simp]
def Var?.SSplit.rightCtx {u v w : Var? α} : u.SSplit v w → Ctx? α → Ctx? α
  | .left _, Γ => Γ.erase
  | .right _, Γ | .sboth _, Γ => Γ

def Var?.SSplit.lift {u v w : Var? α} (Γ : Ctx? α) (hΓ : quant u ≤ quant Γ)
  : (h : u.SSplit v w) → Γ.SSplit (h.leftCtx Γ) (h.rightCtx Γ)
  | .left _ => Γ.erase_right
  | .right _ => Γ.erase_left
  | .sboth h => Γ.both (hΓ := ⟨le_trans h.copy.copy_le_quant hΓ⟩)
