import Refinery.Term.Extrinsic.Wk
import Refinery.Term.Extrinsic.Effect

namespace Refinery

open HasCommRel

namespace Term

abbrev RWS (φ α) := Ctx? α → Ty α → Term φ (Ty α) → Term φ (Ty α) → Prop

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

class RWS.IsWt (R : RWS φ α) : Prop where
  left_wt {Γ A a b} (hab : R Γ A a b) : Term.IsWt Γ A a
  right_wt {Γ A a b} (hab : R Γ A a b) : Term.IsWt Γ A b

instance RWS.instIsWtBot : IsWt (φ := φ) ⊥ where
  left_wt := False.elim
  right_wt := False.elim

theorem RWS.IsWt.mk' (R : RWS φ α)
  (both_wt : ∀ {Γ A a b}, R Γ A a b → Term.IsWt Γ A a ∧ Term.IsWt Γ A b)
  : R.IsWt where
  left_wt hab := (both_wt hab).left
  right_wt hab := (both_wt hab).right

inductive RWS.uniform (R : RWS φ α) : RWS φ α
  | let₁ {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    uniform R Γr A a a' → uniform R (Γl.cons ⟨A, ⊤⟩) B b b'
      → uniform R Γ B (.let₁ a A b) (.let₁ a' A b')
  | let₂ {Γ Γl Γr A B C a b a' b'} :
    Γ.SSplit Γl Γr →
    uniform R Γr (.tensor A B) a a' → uniform R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C b b'
      → uniform R Γ C (.let₂ a A B b) (.let₂ a' A B b')
  | pair {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    uniform R Γl A a a' → uniform R Γr B b b' → uniform R Γ (.tensor A B) (.pair a b) (.pair a' b')
  | inl {Γ A B a a'} : uniform R Γ A a a' → uniform R Γ (.coprod A B) (.inl A B a) (.inl A B a')
  | inr {Γ A B b b'} : uniform R Γ B b b' → uniform R Γ (.coprod A B) (.inr A B b) (.inr A B b')
  | abort {Γ A a a'} : uniform R Γ .empty a a' → uniform R Γ A (.abort A a) (.abort A a')
  | iter {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    Γl.copy → Γl.del →
    uniform R Γr A a a' →
    uniform R (Γl.cons ⟨A, ⊤⟩) (.coprod B A) b b' →
    uniform R Γ B (.iter a A B b) (.iter a' A B b')
  | pos_unif {Γ Γc Γl Γm Γr e e' A B X a b b'} :
    Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Γc.copy → Γc.del → e ∈ S.iterative → e' ⇀ e →
    (Γr ⊢ a : A) → a.HasEff e → ((Γm.cons ⟨A, ⊤⟩) ⊢ s : X) → s.HasEff e' →
    ((Γl.cons ⟨X, ⊤⟩) ⊢ b : B.coprod X) → b.HasEff e →
    ((Γc.cons ⟨A, ⊤⟩) ⊢ b' : B.coprod A) → b'.HasEff e →
    uniform R (Γc.cons ⟨A, ⊤⟩) (.coprod B X)
      (.let₁ s X (↑¹ b))
      (.case b' B A (.inl B X (.bv 0)) (.inr B X (↑¹ s))) →
    uniform R Γ B (.let₁ a A (.iter s X B (↑¹ b))) (.iter a A B b')
  | neg_unif {Γ Γc Γl Γm Γr e e' A B X a b b'} :
    Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Γc.copy → Γc.del → e ∈ S.iterative → e' ↽ e →
    (Γr ⊢ a : A) → a.HasEff e → ((Γm.cons ⟨A, ⊤⟩) ⊢ s : X) → s.HasEff e' →
    ((Γl.cons ⟨X, ⊤⟩) ⊢ b : B.coprod X) → b.HasEff e →
    ((Γc.cons ⟨A, ⊤⟩) ⊢ b' : B.coprod A) → b'.HasEff e →
    uniform R (Γc.cons ⟨A, ⊤⟩) (.coprod B X)
      (.case b' B A (.inl B X (.bv 0)) (.inr B X (↑¹ s)))
      (.let₁ s X (↑¹ b)) →
    uniform R Γ B (.iter a A B b') (.let₁ a A (.iter s X B (↑¹ b)))
  | base {Γ A a b} : R Γ A a b → (Γ ⊢ a : A) → (Γ ⊢ b : A) → uniform R Γ A a b
  | refl {Γ a A} : (Γ ⊢ a : A) → uniform R Γ A a a
  | trans {Γ a b c A} : uniform R Γ A a b → uniform R Γ A b c → uniform R Γ A a c

theorem RWS.uniform.wt {R : RWS φ α} {Γ A a a'} (h : uniform R Γ A a a')
  : Term.IsWt Γ A a ∧ Term.IsWt Γ A a' := by induction h with
  | base | refl => constructor <;> constructor <;> assumption
  | pos_unif hΓ hΓc hc hd he hcomm da hae ds hse db hbe db' hbe' hrw I =>
    rename_i s Γ Γc Γl Γm Γr e e' A B X a b b'
    constructor <;> constructor
    · apply Deriv.let₁ hΓ da
      have _ := hΓc.left_copy
      have _ := hΓc.left_del
      apply Deriv.iter (hΓc.cons (.right _)) inferInstance inferInstance ds (db.wk1 ⟨A, 0⟩)
    · apply Deriv.iter hΓ inferInstance inferInstance da db'
  | neg_unif hΓ hΓc hc hd he hcomm da hae ds hse db hbe db' hbe' hrw I =>
    rename_i s Γ Γc Γl Γm Γr e e' A B X a b b'
    constructor <;> constructor
    · apply Deriv.iter hΓ inferInstance inferInstance da db'
    · apply Deriv.let₁ hΓ da
      have _ := hΓc.left_copy
      have _ := hΓc.left_del
      apply Deriv.iter (hΓc.cons (.right _)) inferInstance inferInstance ds (db.wk1 ⟨A, 0⟩)
  | _ =>
    simp only [Term.IsWt] at *
    cases_type* And Nonempty
    constructor <;> constructor
    <;> first | assumption | (constructor <;> first | exact S.top_iterative | assumption)

inductive RWS.swap (R : RWS φ α) : RWS φ α
  | mk {Γ A a b} : R Γ A b a → swap R Γ A a b

theorem RWS.swap.get {R : RWS φ α} {Γ A a b} (h : swap R Γ A a b)
  : R Γ A b a := by cases h; assumption

theorem RWS.swap_iff {R : RWS φ α} {Γ A a b} : swap R Γ A a b ↔ R Γ A b a :=
  ⟨RWS.swap.get, RWS.swap.mk⟩

inductive RWS.equiv (R : RWS φ α) : RWS φ α
  | mk {Γ A a b} : R Γ A a b → R Γ A b a → equiv R Γ A a b

-- instance RWS.uniform.instWt (R : RWS φ α) : RWS.IsWt (RWS.uniform R) where
--   left_wt h := (RWS.uniform.wt h).left
--   right_wt h := (RWS.uniform.wt h).right

-- inductive Rewrite : RWS φ α
--   | let_op {Γ Γl Γr A B C a c} :
--     Γ.SSplit Γl Γr → S.IsFn f e A B → (Γr ⊢ a : A) → (Γl.cons ⟨B, ⊤⟩ ⊢ c : C) →
--     Rewrite Γ C (.let₁ (.op f a) A c) (.let₁ a A (.let₁ (.op f (.bv 0)) B (↑¹ c)))
--   -- | let_let₁ {Γ Γc Γl Γm Γr} :
--   --   Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Rewrite R _ _ .invalid .invalid
