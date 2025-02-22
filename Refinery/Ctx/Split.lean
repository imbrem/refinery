import Refinery.Ctx.Basic

namespace Refinery

variable [HasQuant α] [PartialOrder ε]

inductive Var?.Split : Var? α ε → Var? α ε → Var? α ε → Type _
  | left {v w} (h : v ≤ w) (e) : Split v w ⟨v.ty, 0, e⟩
  | right {v w} (h : v ≤ w) (e) : Split v ⟨v.ty, 0, e⟩ w
  | sboth {u v w} : u.scopy → u ≤ v → u ≤ w → Split u v w

inductive Ctx?.Split : Ctx? α ε → Ctx? α ε → Ctx? α ε → Type _ where
  | nil : Ctx?.Split .nil .nil .nil
  | cons {Γ Δ Ξ v l r} (h : Split Γ Δ Ξ) (hvw : v.Split l r)
    : Split (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)
