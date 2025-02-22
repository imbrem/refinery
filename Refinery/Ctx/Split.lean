import Refinery.Ctx.Basic

namespace Refinery

variable [HasQuant α]

inductive Var?.Split : Var? α → Var? α → Var? α → Type _
  | left {v w} (h : v ≤ w) : Split v w v.erase
  | right {v w} (h : v ≤ w) : Split v v.erase w
  | sboth {u v w} : u.scopy → u ≤ v → u ≤ w → Split u v w

inductive Ctx?.Split : Ctx? α → Ctx? α → Ctx? α → Type _ where
  | nil : Ctx?.Split .nil .nil .nil
  | cons {Γ Δ Ξ v l r} (h : Split Γ Δ Ξ) (hvw : v.Split l r)
    : Split (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)
