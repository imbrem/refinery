import Refinery.Ty
import Discretion.EffectSystem.Basic

namespace Refinery

class Signature (φ : Type _) (α : outParam (Type _)) (ε : outParam (Type _))
  extends IterEffectSystem ε, HasQuant α
  where
  src : φ → Ty α
  trg : φ → Ty α
  eff : φ → ε

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]

structure Signature.IsFn (f : φ) (e : ε) (A B : Ty α) where
  src : A = src f
  trg : B = trg f
  eff : eff f ≤ e

theorem Signature.IsFn.mono {f : φ} {e e' : ε} {A B : Ty α} (h : IsFn f e A B) (h' : e ≤ e')
  : IsFn f e' A B := ⟨h.src, h.trg, le_trans h.eff h'⟩

theorem Signature.IsFn.top {f : φ} {e : ε} {A B : Ty α} (h : IsFn f e A B) : IsFn f ⊤ A B
  := h.mono le_top

end Refinery
