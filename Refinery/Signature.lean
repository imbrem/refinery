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

class Signature.FnEff (e : ε) (f : φ) : Prop where
  eff : eff f ≤ e

attribute [simp] Signature.FnEff.eff

theorem Signature.FnEff.mono {e e' : ε} (he : e ≤ e') {f : φ} (h : FnEff e f) : FnEff e' f
  := ⟨le_trans h.eff he⟩

@[simp]
instance Signature.FnEff.instTop {f : φ} : FnEff ⊤ f where
  eff := le_top

class Signature.FnTy (f : φ) (A B : Ty α) : Prop where
  src : src f = A
  trg : trg f = B

class Signature.IsFn (f : φ) (e : ε) (A B : Ty α) : Prop extends FnTy f A B, FnEff e f where

instance Signature.IsFn.instMk {f : φ} {e : ε} {A B : Ty α} [h : FnTy f A B] [he : FnEff e f]
  : IsFn f e A B := ⟨⟩

theorem Signature.IsFn.mono {f : φ} {e e' : ε} {A B : Ty α} (h : IsFn f e A B) (he : e ≤ e')
  : IsFn f e' A B := have _ := h.toFnEff.mono he; ⟨⟩

end Refinery
