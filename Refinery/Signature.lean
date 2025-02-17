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
