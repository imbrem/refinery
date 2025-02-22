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

def Signature.HasEff (e : ε) (f : φ) := eff f ≤ e

theorem Signature.HasEff.mono {e e' : ε} (he : e ≤ e') {f : φ} (h : HasEff e f) : HasEff e' f
  := le_trans h he

structure Signature.IsFn (f : φ) (e : ε) (A B : Ty α) where
  src : A = src f
  trg : B = trg f
  eff : HasEff e f

attribute [simp] Signature.IsFn.eff

theorem Signature.IsFn.withEff {f : φ} {e e' : ε} {A B : Ty α} (h : IsFn f e A B) (he : HasEff e' f)
  : IsFn f e' A B := ⟨h.src, h.trg, he⟩

theorem Signature.IsFn.mono {f : φ} {e e' : ε} {A B : Ty α} (h : IsFn f e A B) (he : e ≤ e')
  : IsFn f e' A B := ⟨h.src, h.trg, h.eff.mono he⟩

theorem Signature.IsFn.top {f : φ} {e : ε} {A B : Ty α} (h : IsFn f e A B) : IsFn f ⊤ A B
  := h.mono le_top

end Refinery
