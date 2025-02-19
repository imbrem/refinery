import Refinery.Ctx.Basic
import Refinery.Signature
import Refinery.Term.Syntax

namespace Refinery

open HasQuant

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive Deriv : ε → Ctx? α ε → Ty α → Term φ (Ty α) → Type _
  | bv {Γ} : Γ.At ⟨A, 1, e⟩ n → Deriv e Γ A (.bv n)
  | op {Γ e A B f a} : S.IsFn f e A B → Deriv e Γ A a → Deriv e Γ B (.op f a)
  | let₁ {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γr Γl →
    Deriv e Γl A a → Deriv e (Γr.cons ⟨A, ⊤, ⊥⟩) B b → Deriv e Γ B (.let₁ a A b)
  | unit {Γ} : Γ.Wk .nil → Deriv e Γ .unit .unit
  | pair {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γl Γr →
    Deriv e Γl A a → Deriv e Γr B b → Deriv e Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr e A B C a b} :
    Γ.PSSplit Γr Γl →
    Deriv e Γl (.tensor A B) a → Deriv e ((Γr.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩) C b
      → Deriv e Γ C (.let₂ a A B b)
  | inl {Γ e A B a} : Deriv e Γ A a → Deriv e Γ (.coprod A B) (.inl A B a)
  | inr {Γ e A B b} : Deriv e Γ B b → Deriv e Γ (.coprod A B) (.inr A B b)
  | case {Γ Γl Γr e A B C a b c} :
    Γ.PSSplit Γl Γr →
    Deriv e Γr (.coprod A B) a → Deriv e (Γl.cons ⟨A, ⊤, ⊥⟩) C b → Deriv e (Γl.cons ⟨B, ⊤, ⊥⟩) C c
      → Deriv e Γ C (.case a A B b c)
  | abort {Γ e A a} : Deriv e Γ .empty a → Deriv e Γ A (.abort A a)
  | iter {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γr Γl →
    e ∈ S.iterative →
    Γr.copy → Γr.del →
    Deriv e Γl A a → Deriv e (Γr.cons ⟨A, ⊤, ⊥⟩) (.coprod B A) b → Deriv e Γ B (.iter a A B b)

notation Γ "⊢[" e "]" a ":" A => Deriv e Γ A a

def Deriv.mono {e e' : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)} (he : e ≤ e')
  : (Γ ⊢[e] a : A) → (Γ ⊢[e'] a : A)
  | .bv hv => .bv (hv.wkOut (Var?.wk_eff _ _ he))
  | .op hf da => .op (hf.mono he) (da.mono he)
  | .let₁ dΓ da db => .let₁ dΓ (da.mono he) (db.mono he)
  | .unit dΓ => .unit dΓ
  | .pair dΓ da db => .pair dΓ (da.mono he) (db.mono he)
  | .let₂ dΓ da db => .let₂ dΓ (da.mono he) (db.mono he)
  | .inl da => .inl (da.mono he)
  | .inr db => .inr (db.mono he)
  | .case dΓ da db dc => .case dΓ (da.mono he) (db.mono he) (dc.mono he)
  | .abort da => .abort (da.mono he)
  | .iter dΓ hei hc hd da db =>
    .iter dΓ (S.iterative_is_upper he hei) hc hd (da.mono he) (db.mono he)

abbrev Deriv.top {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢[e] a : A) : (Γ ⊢[⊤] a : A) := D.mono le_top
