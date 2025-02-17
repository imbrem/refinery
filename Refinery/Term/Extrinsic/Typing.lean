import Refinery.Ctx.Basic
import Refinery.Signature
import Refinery.Term.Syntax

namespace Refinery

open HasQuant

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive Wf : Ctx? α ε → Ty α → Term φ → Type _
  | bv {Γ} : Γ.At ⟨A, 1, e⟩ n → Wf Γ A (.bv n)
  | op {Γ e A B f a} : S.IsFn f e A B → Wf Γ A a → Wf Γ B (.op f a)
  | let₁ {Γ Γl Γr A B a b} :
    Γ.PSSplit Γr Γl →
    Wf Γl A a → Wf (Γr.cons ⟨A, ⊤, ⊥⟩) B b → Wf Γ B (.let₁ a b)
  | unit {Γ} : Γ.Wk .nil → Wf Γ .unit .unit
  | pair {Γ Γl Γr A B a b} :
    Γ.PSSplit Γl Γr →
    Wf Γl A a → Wf Γr B b → Wf Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr A B C a b} :
    Γ.PSSplit Γr Γl →
    Wf Γl (.tensor A B) a → Wf ((Γr.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩) C b → Wf Γ C (.let₂ a b)
  | inl {Γ A B a} : Wf Γ A a → Wf Γ (.coprod A B) (.inl a)
  | inr {Γ A B b} : Wf Γ B b → Wf Γ (.coprod A B) (.inr b)
  | case {Γ Γl Γr A B C a b c} :
    Γ.PSSplit Γl Γr →
    Wf Γr (.coprod A B) a → Wf (Γl.cons ⟨A, ⊤, ⊥⟩) C b → Wf (Γl.cons ⟨B, ⊤, ⊥⟩) C c
      → Wf Γ C (.case a b c)
  | abort {Γ A a} : Wf Γ .empty a → Wf Γ A (.abort a)
  | iter {Γ Γl Γr A B a b} :
    Γ.PSSplit Γr Γl →
    Γr.copy → Γr.del →
    Wf Γl A a → Wf (Γr.cons ⟨A, ⊤, ⊥⟩) (.coprod B A) b → Wf Γ B (.iter a b)

notation Γ "⊢" a ":" A => Wf Γ A a

inductive Deriv : ε → Ctx? α ε → Ty α → Term φ → Type _
  | bv {Γ} : Γ.At ⟨A, 1, e⟩ n → Deriv e Γ A (.bv n)
  | op {Γ e A B f a} : S.IsFn f e A B → Deriv e Γ A a → Deriv e Γ B (.op f a)
  | let₁ {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γr Γl →
    Deriv e Γl A a → Deriv e (Γr.cons ⟨A, ⊤, ⊥⟩) B b → Deriv e Γ B (.let₁ a b)
  | unit {Γ} : Γ.Wk .nil → Deriv e Γ .unit .unit
  | pair {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γl Γr →
    Deriv e Γl A a → Deriv e Γr B b → Deriv e Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr e A B C a b} :
    Γ.PSSplit Γr Γl →
    Deriv e Γl (.tensor A B) a → Deriv e ((Γr.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩) C b
      → Deriv e Γ C (.let₂ a b)
  | inl {Γ e A B a} : Deriv e Γ A a → Deriv e Γ (.coprod A B) (.inl a)
  | inr {Γ e A B b} : Deriv e Γ B b → Deriv e Γ (.coprod A B) (.inr b)
  | case {Γ Γl Γr e A B C a b c} :
    Γ.PSSplit Γl Γr →
    Deriv e Γr (.coprod A B) a → Deriv e (Γl.cons ⟨A, ⊤, ⊥⟩) C b → Deriv e (Γl.cons ⟨B, ⊤, ⊥⟩) C c
      → Deriv e Γ C (.case a b c)
  | abort {Γ e A a} : Deriv e Γ .empty a → Deriv e Γ A (.abort a)
  | iter {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γr Γl →
    e ∈ S.iterative →
    Γr.copy → Γr.del →
    Deriv e Γl A a → Deriv e (Γr.cons ⟨A, ⊤, ⊥⟩) (.coprod B A) b → Deriv e Γ B (.iter a b)

notation Γ "⊢[" e "]" a ":" A => Deriv e Γ A a

def Deriv.toWf {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ} : (Γ ⊢[e] a : A) → (Γ ⊢ a : A)
  | .bv hv => Wf.bv hv
  | .op hf da => Wf.op hf (Deriv.toWf da)
  | .let₁ dΓ da db => Wf.let₁ dΓ (Deriv.toWf da) (Deriv.toWf db)
  | .unit dΓ => Wf.unit dΓ
  | .pair dΓ da db => Wf.pair dΓ (Deriv.toWf da) (Deriv.toWf db)
  | .let₂ dΓ da db => Wf.let₂ dΓ (Deriv.toWf da) (Deriv.toWf db)
  | .inl da => Wf.inl (Deriv.toWf da)
  | .inr db => Wf.inr (Deriv.toWf db)
  | .case dΓ da db dc => Wf.case dΓ (Deriv.toWf da) (Deriv.toWf db) (Deriv.toWf dc)
  | .abort da => Wf.abort (Deriv.toWf da)
  | .iter dΓ _ dΓrc dΓrd da db => Wf.iter dΓ dΓrc dΓrd (Deriv.toWf da) (Deriv.toWf db)
