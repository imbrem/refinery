import Refinery.Ctx.Minimal
import Refinery.Term.Extrinsic.Typing

namespace Refinery

open HasQuant

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive SDeriv : Ctx? α → Ty α → Term φ (Ty α) → Type _
  | bv {Γ} : Γ.SAt ⟨A, 1⟩ n → SDeriv Γ A (.bv n)
  | op {Γ A B f a} : S.FnTy f A B → SDeriv Γ A a → SDeriv Γ B (.op f a)
  | let₁ {Γ Γl Γr A B a b} :
    Γ.SSplit Γl Γr →
    SDeriv Γr A a → SDeriv (Γl.cons ⟨A, ⊤⟩) B b → SDeriv Γ B (.let₁ a A b)
  | unit {Γ} : Γ.IsZero → SDeriv Γ .unit .unit
  | pair {Γ Γl Γr A B a b} :
    Γ.SSplit Γl Γr →
    SDeriv Γl A a → SDeriv Γr B b → SDeriv Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr A B C a b} :
    Γ.SSplit Γl Γr →
    SDeriv Γr (.tensor A B) a → SDeriv ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C b
      → SDeriv Γ C (.let₂ a A B b)
  | inl {Γ A B a} : SDeriv Γ A a → SDeriv Γ (.coprod A B) (.inl A B a)
  | inr {Γ A B b} : SDeriv Γ B b → SDeriv Γ (.coprod A B) (.inr A B b)
  | case {Γ Γl Γr A B C a b c} :
    Γ.SSplit Γl Γr →
    SDeriv Γr (.coprod A B) a → SDeriv (Γl.cons ⟨A, ⊤⟩) C b → SDeriv (Γl.cons ⟨B, ⊤⟩) C c
      → SDeriv Γ C (.case a A B b c)
  | abort {Γ A a} : SDeriv Γ .empty a → SDeriv Γ A (.abort A a)
  | iter {Γ Γl Γr A B a b} :
    Γ.SSplit Γl Γr →
    Γl.copy → Γl.del →
    SDeriv Γr A a → SDeriv (Γl.cons ⟨A, ⊤⟩) (.coprod B A) b → SDeriv Γ B (.iter a A B b)

notation Γ "⊢ₛ" a ":" A => SDeriv Γ A a

def SDeriv.unstrict {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} : (Γ ⊢ₛ a : A) → Γ ⊢ a : A
  | .bv hv => .bv hv.unstrict
  | .op hf da => .op hf da.unstrict
  | .let₁ hΓ da db => .let₁ hΓ da.unstrict db.unstrict
  | .unit hv => .unit hv.del
  | .pair hΓ da db => .pair hΓ da.unstrict db.unstrict
  | .let₂ hΓ da db => .let₂ hΓ da.unstrict db.unstrict
  | .inl da => .inl da.unstrict
  | .inr db => .inr db.unstrict
  | .case hΓ da db dc => .case hΓ da.unstrict db.unstrict dc.unstrict
  | .abort da => .abort da.unstrict
  | .iter hΓ hc hd da db => .iter hΓ hc hd da.unstrict db.unstrict

def SDeriv.cast {Γ Γ' : Ctx? α} {A A' : Ty α} {a a' : Term φ (Ty α)}
  (hΓ : Γ = Γ') (hA : A = A') (ha : a = a')
  (D : Γ ⊢ₛ a : A) : (Γ' ⊢ₛ a' : A') := hΓ ▸ hA ▸ ha ▸ D

abbrev SDeriv.cast_ctx {Γ Γ' : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (hΓ : Γ = Γ') (D : Γ ⊢ₛ a : A) : Γ' ⊢ₛ a : A := D.cast hΓ rfl rfl

abbrev SDeriv.cast_ty {Γ : Ctx? α} {A A' : Ty α} {a : Term φ (Ty α)}
  (hA : A = A') (D : Γ ⊢ₛ a : A) : Γ ⊢ₛ a : A' := D.cast rfl hA rfl

abbrev SDeriv.cast_term {Γ : Ctx? α} {A : Ty α} {a a' : Term φ (Ty α)}
  (ha : a = a') (D : Γ ⊢ₛ a : A) : Γ ⊢ₛ a' : A := D.cast rfl rfl ha

@[simp]
theorem SDeriv.cast_rfl {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ a : A)
  : D.cast rfl rfl rfl = D := rfl

def IsSWt (Γ : Ctx? α) (A : Ty α) (a : Term φ (Ty α)) : Prop := Nonempty (Γ ⊢ₛ a : A)

@[match_pattern]
theorem SDeriv.wt {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ a : A)
  : IsSWt Γ A a := ⟨D⟩

def SDeriv.bv_at {Γ : Ctx? α} {A : Ty α} {n : ℕ} (D : Γ ⊢ₛ (.bv (φ := φ) n) : A)
  : Γ.SAt ⟨A, 1⟩ n := match D with | .bv hv => hv

theorem SDeriv.ueq {Γ Γ' : Ctx? α} {A A' : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢ₛ a : A) (D' : Γ' ⊢ₛ a : A') (hΓ : Γ.TyEq Γ')
  : Γ.UEq Γ' := by induction D generalizing Γ' A' with
  | bv hv => cases D' with | bv hv' =>
    apply hv.ueq_of_ty_eq; assumption; cases hv.ty_eq_out hΓ hv'; assumption; simp
  | unit => cases D'; apply Ctx?.TyEq.zero_ueq <;> assumption
  | _ =>
    cases D'
    first | (apply_assumption <;> assumption)
          | {
      apply Ctx?.SSplit.in_ueq; assumption; assumption
      (first | apply_assumption
             | (apply Ctx?.UEq.tail; apply_assumption)
             | (apply Ctx?.UEq.tail; apply Ctx?.UEq.tail; apply_assumption))
      assumption
      (try simp only [Ctx?.TyEq.cons_iff, and_true])
      apply Ctx?.SSplit.shunt_left_ty_eq <;> assumption
      apply_assumption
      assumption
      apply Ctx?.SSplit.shunt_right_ty_eq <;> assumption
    }

theorem SDeriv.eq_of_zqeq {Γ Γ' : Ctx? α} {A A' : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢ₛ a : A) (D' : Γ' ⊢ₛ a : A') (hΓ : Γ.ZQEq Γ')
  : Γ = Γ' := hΓ.ueq (D.ueq D' hΓ.ty_eq)

end Term

end Refinery
