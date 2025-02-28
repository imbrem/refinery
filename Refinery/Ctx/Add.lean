import Refinery.Ctx.Basic
import Refinery.Ctx.SSplit
namespace Refinery

-- def Var?.add (v w : Var? α ε) : Var? α ε := ⟨v.ty, v.q + w.q, v.eff⟩

-- structure Var?.compat (v w : Var? α ε) : Prop where
--   ty : v.ty = w.ty
--   eff : v.eff = w.eff

-- @[simp]
-- theorem Var?.compat.refl (v : Var? α ε) : Var?.compat v v := ⟨rfl, rfl⟩

-- theorem Var?.compat.symm {v w : Var? α ε} (h : Var?.compat v w) : Var?.compat w v
--   := ⟨h.ty.symm, h.eff.symm⟩

-- theorem Var?.compat.trans {u v w : Var? α ε} (huv : Var?.compat u v) (hvw : Var?.compat v w)
--   : Var?.compat u w := ⟨huv.ty.trans hvw.ty, huv.eff.trans hvw.eff⟩

-- theorem Var?.compat.erase_left {v w : Var? α ε} (h : Var?.compat v w) : Var?.compat v.erase w
--   := ⟨h.ty, h.eff⟩

-- theorem Var?.compat.erase_rigth {v w : Var? α ε} (h : Var?.compat v w) : Var?.compat v w.erase
--   := ⟨h.ty, h.eff⟩

-- @[simp]
-- theorem Var?.compat.self_erase_left (v : Var? α ε) : Var?.compat v.erase v := ⟨rfl, rfl⟩

-- @[simp]
-- theorem Var?.compat.self_erase_right (v : Var? α ε) : Var?.compat v v.erase := ⟨rfl, rfl⟩

-- structure Var?.qcompat (v w : Var? α ε) extends compat v w : Prop where
--   q : v.q = w.q ∨ (v.q = 0 ∨ w.q = 0)

-- @[simp]
-- theorem Var?.qcompat.refl (v : Var? α ε) : Var?.qcompat v v := ⟨Var?.compat.refl v, Or.inl rfl⟩

-- theorem Var?.qcompat.symm {v w : Var? α ε} (h : Var?.qcompat v w) : Var?.qcompat w v
--   := ⟨Var?.compat.symm h.tocompat, match h.q with
--     | Or.inl h => Or.inl h.symm
--     | Or.inr (Or.inl h) => Or.inr (Or.inr h)
--     | Or.inr (Or.inr h) => Or.inr (Or.inl h)⟩

-- instance Var?.instAdd : Add (Var? α ε) where
--   add := Var?.add

-- theorem Var?.add_def (v w : Var? α ε) : v + w = ⟨v.ty, v.q + w.q, v.eff⟩ := rfl

-- @[simp]
-- theorem Var?.add_erase (v : Var? α ε) : v + v.erase = v := by simp [add_def]

-- @[simp]
-- theorem Var?.erase_add (v : Var? α ε) : v.erase + v = v := by simp [add_def]

-- instance Var?.instAddSemigroup : AddSemigroup (Var? α ε) where
--   add_assoc u v w := by simp [Var?.add_def, add_assoc]

-- def Ctx?.add (Γ Δ : Ctx? α ε) : Ctx? α ε := match Γ, Δ with
--   | .nil, Δ => Δ
--   | Γ, .nil => Γ
--   | .cons Γ v, .cons Δ w => .cons (Γ.add Δ) (v + w)

-- inductive Ctx?.compat : Ctx? α ε → Ctx? α ε → Prop where
--   | nil : Ctx?.compat .nil .nil
--   | cons {Γ Δ} {v w : Var? α ε} (hΓ : Ctx?.compat Γ Δ) (hv : Var?.compat v w)
--     : Ctx?.compat (Γ.cons v) (Δ.cons w)

-- @[simp]
-- theorem Ctx?.compat.refl (Γ : Ctx? α ε) : Ctx?.compat Γ Γ := by
--   induction Γ <;> constructor <;> simp [*]

-- theorem Ctx?.compat.symm {Γ Δ : Ctx? α ε} (h : Ctx?.compat Γ Δ) : Ctx?.compat Δ Γ := by
--   induction h <;> constructor <;> simp [Var?.compat.symm, *]

-- theorem Ctx?.compat.trans {Γ Δ Ξ : Ctx? α ε} (hΓΔ : Ctx?.compat Γ Δ) (hΔΞ : Ctx?.compat Δ Ξ)
--   : Ctx?.compat Γ Ξ := by
--   induction hΓΔ generalizing Ξ <;> cases hΔΞ
--   <;> constructor; apply_assumption; assumption; apply Var?.compat.trans <;> assumption

-- inductive Ctx?.qcompat : Ctx? α ε → Ctx? α ε → Prop where
--   | nil : Ctx?.qcompat .nil .nil
--   | cons {Γ Δ} {v w : Var? α ε} (hΓ : Ctx?.qcompat Γ Δ) (hv : Var?.qcompat v w)
--     : Ctx?.qcompat (Γ.cons v) (Δ.cons w)

-- @[simp]
-- theorem Ctx?.qcompat.refl (Γ : Ctx? α ε) : Ctx?.qcompat Γ Γ := by
--   induction Γ <;> constructor <;> simp [*]

-- @[simp]
-- theorem Ctx?.qcompat.symm (Γ Δ : Ctx? α ε) (h : Ctx?.qcompat Γ Δ) : Ctx?.qcompat Δ Γ := by
--   induction h <;> constructor <;> simp [Var?.qcompat.symm, *]

-- instance Ctx?.instAdd : Add (Ctx? α ε) where
--   add := Ctx?.add

-- @[simp]
-- theorem Ctx?.add_nil (Γ : Ctx? α ε) : Γ + .nil = Γ := by cases Γ <;> rfl

-- @[simp]
-- theorem Ctx?.nil_add (Γ : Ctx? α ε) : .nil + Γ = Γ := by cases Γ <;> rfl

-- @[simp]
-- theorem Ctx?.cons_add_cons (Γ Δ : Ctx? α ε) (v w : Var? α ε)
--   : Γ.cons v + Δ.cons w = .cons (Γ + Δ) (v + w) := rfl

-- @[simp]
-- theorem Ctx?.add_erase (Γ : Ctx? α ε) : Γ + Γ.erase = Γ := by induction Γ <;> simp [*]

-- instance Ctx?.instZero : Zero (Ctx? α ε) where
--   zero := .nil

-- instance AddMonoid : AddMonoid (Ctx? α ε) where
--   add_assoc Γ Δ Ξ := by induction Γ generalizing Δ Ξ <;> cases Δ <;> cases Ξ <;> simp [add_assoc, *]
--   zero_add Γ := Γ.nil_add
--   add_zero Γ := Γ.add_nil
--   nsmul := nsmulRec

-- variable [HasQuant α]

-- open HasQuant

-- @[simp]
-- theorem Var?.PSSplit.trg_compat {u v w : Var? α ε} (h : u.PSSplit v w) : v.compat w := by
--   cases h <;> simp

-- @[simp]
-- theorem Var?.PSSplit.left_compat {u v w : Var? α ε} (h : u.PSSplit v w) : u.compat v := by
--   cases h <;> simp

-- @[simp]
-- theorem Var?.PSSplit.right_compat {u v w : Var? α ε} (h : u.PSSplit v w) : u.compat w := by
--   cases h <;> simp

-- @[simp]
-- theorem Var?.add_idem_copy (v : Var? α ε) [hv : v.copy] : v + v = v := by
--   cases v with | mk A q e =>
--   simp only [add_def, mk.injEq, and_true, true_and]
--   cases q using EQuant.casesZero with
--   | zero => rfl
--   | rest q =>
--     simp [copy_iff] at hv
--     cases hv.q using EQuant.le.casesLE_all <;> rfl

-- @[simp]
-- theorem Var?.add_idem_scopy {v : Var? α ε} (hv : v.scopy) : v + v = v := by
--   cases v with | mk A q e =>
--   simp only [add_def, mk.injEq, and_true, true_and]
--   cases hv.q using EQuant.le.casesLE_all <;> rfl

-- theorem Var?.PSSplit.add_eq {u v w : Var? α ε} (h : u.PSSplit v w) : v + w = u := by
--   induction h <;> simp [*]

-- theorem Ctx?.PSSplit.add_eq {Γ Δ Ξ : Ctx? α ε} (h : Γ.PSSplit Δ Ξ) : Δ + Ξ = Γ := by
--   induction h with | nil => rfl | cons hΓ hvw I => simp [I, hvw.add_eq]
