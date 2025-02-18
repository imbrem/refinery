import Refinery.Term.Extrinsic.Typing
import Refinery.Ctx.Basic

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

def Deriv.wk {e : ε} {Γ Δ : Ctx? α ε} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ}
  : (Δ ⊢[e] a : A) → (Γ ⊢[e] a.ren ρ : A)
  | .bv hv => .bv (hv.wkIn ρ)
  | .op hf da => .op hf (da.wk ρ)
  | _ => sorry

end Term

end Refinery
