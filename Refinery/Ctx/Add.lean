import Refinery.Ctx.Basic

namespace Refinery

def Var?.add (v w : Var? α ε) : Var? α ε := ⟨v.ty, v.q + w.q, v.eff⟩

instance Var?.instAdd : Add (Var? α ε) where
  add := Var?.add

theorem Var?.add_def (v w : Var? α ε) : v + w = ⟨v.ty, v.q + w.q, v.eff⟩ := rfl

@[simp]
theorem Var?.add_erase (v : Var? α ε) : v + v.erase = v := by simp [add_def]

@[simp]
theorem Var?.erase_add (v : Var? α ε) : v.erase + v = v := by simp [add_def]

instance Var?.instAddSemigroup : AddSemigroup (Var? α ε) where
  add_assoc u v w := by simp [Var?.add_def, add_assoc]

def Ctx?.add (Γ Δ : Ctx? α ε) : Ctx? α ε := match Γ, Δ with
  | .nil, Δ => Δ
  | Γ, .nil => Γ
  | .cons Γ v, .cons Δ w => .cons (Γ.add Δ) (v + w)

instance Ctx?.instAdd : Add (Ctx? α ε) where
  add := Ctx?.add

@[simp]
theorem Ctx?.add_nil (Γ : Ctx? α ε) : Γ + .nil = Γ := by cases Γ <;> rfl

@[simp]
theorem Ctx?.nil_add (Γ : Ctx? α ε) : .nil + Γ = Γ := by cases Γ <;> rfl

@[simp]
theorem Ctx?.cons_add_cons (Γ Δ : Ctx? α ε) (v w : Var? α ε)
  : Γ.cons v + Δ.cons w = .cons (Γ + Δ) (v + w) := rfl

@[simp]
theorem Ctx?.add_erase (Γ : Ctx? α ε) : Γ + Γ.erase = Γ := by induction Γ <;> simp [*]

instance Ctx?.instZero : Zero (Ctx? α ε) where
  zero := .nil

instance AddMonoid : AddMonoid (Ctx? α ε) where
  add_assoc Γ Δ Ξ := by induction Γ generalizing Δ Ξ <;> cases Δ <;> cases Ξ <;> simp [add_assoc, *]
  zero_add Γ := Γ.nil_add
  add_zero Γ := Γ.add_nil
  nsmul := nsmulRec
