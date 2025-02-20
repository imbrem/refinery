import Refinery.Term.Extrinsic.Typing

namespace Refinery

namespace Term

abbrev RWS (φ α ε) := Ctx? α ε → Ty α → Term φ (Ty α) → Term φ (Ty α) → Prop

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

class RWS.IsWt (R : RWS φ α ε) : Prop where
  left_wt {Γ A a b} (hab : R Γ A a b) : Term.IsWt ⊤ Γ A a
  right_wt {Γ A a b} (hab : R Γ A a b) : Term.IsWt ⊤ Γ A b

theorem RWS.IsWt.mk' (R : RWS φ α ε)
  (both_wt : ∀ {Γ A a b}, R Γ A a b → Term.IsWt ⊤ Γ A a ∧ Term.IsWt ⊤ Γ A b)
  : R.IsWt where
  left_wt hab := (both_wt hab).left
  right_wt hab := (both_wt hab).right

inductive RWS.cc (R : RWS φ α ε) : RWS φ α ε
  | base {Γ A a b} : R Γ A a b → cc R Γ A a b
  | refl {Γ e a A} : (Γ ⊢[e] a : A) → cc R Γ A a a
  | symm {Γ a b A} : cc R Γ A a b → cc R Γ A b a
  | trans {Γ a b c A} : cc R Γ A a b → cc R Γ A b c → cc R Γ A a c
  | let₁ {Γ Γl Γr A B a b a' b'} :
    Γ.PSSplit Γl Γr →
    cc R Γr A a a' → cc R (Γl.cons ⟨A, ⊤, ⊥⟩) B b b'
      → cc R Γ B (.let₁ a A b) (.let₁ a' A b')
  | let₂ {Γ Γl Γr A B C a b a' b'} :
    Γ.PSSplit Γl Γr →
    cc R Γr (.tensor A B) a a' → cc R ((Γl.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩) C b b'
      → cc R Γ C (.let₂ a A B b) (.let₂ a' A B b')
  | pair {Γ Γl Γr A B a b a' b'} :
    Γ.PSSplit Γl Γr →
    cc R Γl A a a' → cc R Γr B b b' → cc R Γ (.tensor A B) (.pair a b) (.pair a' b')
  | inl {Γ A B a a'} : cc R Γ A a a' → cc R Γ (.coprod A B) (.inl A B a) (.inl A B a')
  | inr {Γ A B b b'} : cc R Γ B b b' → cc R Γ (.coprod A B) (.inr A B b) (.inr A B b')
  | abort {Γ A a a'} : cc R Γ .empty a a' → cc R Γ A (.abort A a) (.abort A a')
  | iter {Γ Γl Γr A B a b a' b'} :
    Γ.PSSplit Γl Γr →
    Γl.copy → Γl.del →
    cc R Γr A a a' →
    cc R (Γl.cons ⟨A, ⊤, ⊥⟩) (.coprod B A) b b' →
    cc R Γ B (.iter a A B b) (.iter a' A B b')

theorem RWS.cc.wt {R : RWS φ α ε} [RWS.IsWt R] {Γ A a a'} (h : cc R Γ A a a')
  : Term.IsWt ⊤ Γ A a ∧ Term.IsWt ⊤ Γ A a' := by induction h with
  | base R => exact ⟨IsWt.left_wt R, IsWt.right_wt R⟩
  | refl => constructor <;> apply Deriv.wt_top <;> assumption
  | _ =>
    simp only [Term.IsWt] at *
    cases_type* And Nonempty
    constructor <;> constructor
    <;> first | assumption | (constructor <;> first | exact S.top_iterative | assumption)

instance RWS.cc.instWt (R : RWS φ α ε) [RWS.IsWt R] : RWS.IsWt (RWS.cc R) where
  left_wt h := (RWS.cc.wt h).left
  right_wt h := (RWS.cc.wt h).right

inductive Rewrite : RWS φ α ε
  | let_op {Γ Γl Γr A B C a c} :
    Γ.PSSplit Γl Γr → S.IsFn f e A B → (Γr ⊢[⊤] a : A) → (Γl.cons ⟨B, ⊤, ⊥⟩ ⊢[⊤] c : C) →
    Rewrite Γ C (.let₁ (.op f a) A c) (.let₁ a A (.let₁ (.op f (.bv 0)) B (↑¹ c)))
  -- | let_let₁ {Γ Γc Γl Γm Γr} :
  --   Γ.PSSplit Γc Γr → Γc.PSSplit Γl Γm → Rewrite R _ _ .invalid .invalid
