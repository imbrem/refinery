import Refinery.Ctx.Basic
import Refinery.Ctx.SSplit
import Refinery.Signature
import Refinery.Term.Syntax
import Refinery.Term.Extrinsic.Effect

namespace Refinery

open HasQuant

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

--TODO: port to Split for hax?

inductive Deriv : Ctx? α → Ty α → Term φ (Ty α) → Type _
  | bv {Γ} : Γ.At ⟨A, 1⟩ n → Deriv Γ A (.bv n)
  | op {Γ A B f a} : S.FnTy f A B → Deriv Γ A a → Deriv Γ B (.op f a)
  | let₁ {Γ Γl Γr A B a b} :
    Γ.SSplit Γl Γr →
    Deriv Γr A a → Deriv (Γl.cons ⟨A, ⊤⟩) B b → Deriv Γ B (.let₁ a A b)
  | unit {Γ} : Γ.del → Deriv Γ .unit .unit
  | pair {Γ Γl Γr A B a b} :
    Γ.SSplit Γl Γr →
    Deriv Γl A a → Deriv Γr B b → Deriv Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr A B C a b} :
    Γ.SSplit Γl Γr →
    Deriv Γr (.tensor A B) a → Deriv ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C b
      → Deriv Γ C (.let₂ a A B b)
  | inl {Γ A B a} : Deriv Γ A a → Deriv Γ (.coprod A B) (.inl A B a)
  | inr {Γ A B b} : Deriv Γ B b → Deriv Γ (.coprod A B) (.inr A B b)
  | case {Γ Γl Γr A B C a b c} :
    Γ.SSplit Γl Γr →
    Deriv Γr (.coprod A B) a → Deriv (Γl.cons ⟨A, ⊤⟩) C b → Deriv (Γl.cons ⟨B, ⊤⟩) C c
      → Deriv Γ C (.case a A B b c)
  | abort {Γ A a} : Deriv Γ .empty a → Deriv Γ A (.abort A a)
  | iter {Γ Γl Γr A B a b} :
    Γ.SSplit Γl Γr →
    Γl.copy → Γl.del →
    Deriv Γr A a → Deriv (Γl.cons ⟨A, ⊤⟩) (.coprod B A) b → Deriv Γ B (.iter a A B b)

notation Γ "⊢" a ":" A => Deriv Γ A a

def Deriv.cast {Γ Γ' : Ctx? α} {A A' : Ty α} {a a' : Term φ (Ty α)}
  (hΓ : Γ = Γ') (hA : A = A') (ha : a = a')
  (D : Γ ⊢ a : A) : (Γ' ⊢ a' : A') := hΓ ▸ hA ▸ ha ▸ D

abbrev Deriv.cast_ctx {Γ Γ' : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (hΓ : Γ = Γ') (D : Γ ⊢ a : A) : Γ' ⊢ a : A := D.cast hΓ rfl rfl

abbrev Deriv.cast_ty {Γ : Ctx? α} {A A' : Ty α} {a : Term φ (Ty α)}
  (hA : A = A') (D : Γ ⊢ a : A) : Γ ⊢ a : A' := D.cast rfl hA rfl

abbrev Deriv.cast_term {Γ : Ctx? α} {A : Ty α} {a a' : Term φ (Ty α)}
  (ha : a = a') (D : Γ ⊢ a : A) : Γ ⊢ a' : A := D.cast rfl rfl ha

def IsWt (Γ : Ctx? α) (A : Ty α) (a : Term φ (Ty α)) : Prop := Nonempty (Γ ⊢ a : A)

@[match_pattern]
theorem Deriv.wt {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ a : A)
  : IsWt Γ A a := ⟨D⟩

def Deriv.bv_at {Γ : Ctx? α} {A : Ty α} {n : ℕ} (D : Γ ⊢ (.bv (φ := φ) n) : A)
  : Γ.At ⟨A, 1⟩ n := match D with | .bv hv => hv

-- theorem IsWt.bv_at {Γ : Ctx? α} {A : Ty α} {n : ℕ} (D : IsWt (φ := φ) e Γ A (.bv n))
--   : Γ.At ⟨A, 1⟩ n := D.elim Deriv.bv_at

theorem Deriv.op_fn {Γ : Ctx? α} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : Γ ⊢ (.op f a) : B) : S.FnTy f (S.src f) B
  := match D with | .op hf da => by cases hf.src; exact hf

theorem IsWt.op_fn {Γ : Ctx? α} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : IsWt Γ B (.op f a)) : S.FnTy f (S.src f) B := D.elim Deriv.op_fn

def Deriv.op_arg {Γ : Ctx? α} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : Γ ⊢ (.op f a) : B) : Γ ⊢ a : S.src f
  := match D with | .op hf da => da.cast_ty hf.src

theorem IsWt.op_arg {Γ : Ctx? α} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : IsWt Γ B (.op f a)) : IsWt Γ (S.src f) a := ⟨(Classical.choice D).op_arg⟩

def Deriv.let₁_splitLeft {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₁ a A b) : B) : Ctx? α
  := match D with | .let₁ (Γl := Γl) .. => Γl

def Deriv.let₁_splitRight {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₁ a A b) : B) : Ctx? α
  := match D with | .let₁ (Γr := Γr) .. => Γr

def Deriv.let₁_split {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₁ a A b) : B) : Γ.SSplit (D.let₁_splitLeft) (D.let₁_splitRight)
  := match D with | .let₁ dΓ _ _ => dΓ

def Deriv.let₁_bind {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₁ a A b) : B) : D.let₁_splitRight ⊢ a : A
  := match D with | .let₁ _ da _ => da

def Deriv.let₁_body {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₁ a A b) : B) : (D.let₁_splitLeft.cons ⟨A, ⊤⟩) ⊢ b : B
  := match D with | .let₁ _ _ db => db

theorem Deriv.unit_wk {Γ : Ctx? α} {A : Ty α} (D : Γ ⊢ .unit (φ := φ) : A) : Γ.del
  := match D with | .unit dΓ => dΓ

theorem IsWt.unit_wk {Γ : Ctx? α} (D : IsWt (φ := φ) Γ A .unit) : Γ.del
  := D.elim Deriv.unit_wk

def Deriv.pair_splitLeft {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.pair a b) : .tensor A B) : Ctx? α
  := match D with | .pair (Γl := Γl) .. => Γl

def Deriv.pair_splitRight {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.pair a b) : .tensor A B) : Ctx? α
  := match D with | .pair (Γr := Γr) .. => Γr

def Deriv.pair_split {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.pair a b) : .tensor A B) : Γ.SSplit (D.pair_splitLeft) (D.pair_splitRight)
  := match D with | .pair dΓ _ _ => dΓ

def Deriv.pair_fst {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.pair a b) : .tensor A B) : D.pair_splitLeft ⊢ a : A
  := match D with | .pair _ da _ => da

def Deriv.pair_snd {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.pair a b) : .tensor A B) : D.pair_splitRight ⊢ b : B
  := match D with | .pair _ _ db => db

def Deriv.let₂_splitLeft {Γ : Ctx? α} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₂ a A B b) : C) : Ctx? α
  := match D with | .let₂ (Γl := Γl) .. => Γl

def Deriv.let₂_splitRight {Γ : Ctx? α} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₂ a A B b) : C) : Ctx? α
  := match D with | .let₂ (Γr := Γr) .. => Γr

def Deriv.let₂_split {Γ : Ctx? α} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₂ a A B b) : C) : Γ.SSplit (D.let₂_splitLeft) (D.let₂_splitRight)
  := match D with | .let₂ dΓ _ _ => dΓ

def Deriv.let₂_bind {Γ : Ctx? α} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₂ a A B b) : C) : D.let₂_splitRight ⊢ a : .tensor A B
  := match D with | .let₂ _ da _ => da

def Deriv.let₂_body {Γ : Ctx? α} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.let₂ a A B b) : C) : (D.let₂_splitLeft.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C
  := match D with | .let₂ _ _ db => db

def Deriv.inl_arg {Γ : Ctx? α} {A B : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢ (.inl A B a) : .coprod A B) : Γ ⊢ a : A
  := match D with | .inl da => da

def Deriv.inr_arg {Γ : Ctx? α} {A B : Ty α} {b : Term φ (Ty α)}
  (D : Γ ⊢ (.inr A B b) : .coprod A B) : Γ ⊢ b : B
  := match D with | .inr db => db

def Deriv.case_splitLeft {Γ : Ctx? α} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢ (.case a A B b c) : C) : Ctx? α
  := match D with | .case (Γl := Γl) .. => Γl

def Deriv.case_splitRight {Γ : Ctx? α} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢ (.case a A B b c) : C) : Ctx? α
  := match D with | .case (Γr := Γr) .. => Γr

def Deriv.case_bind {Γ : Ctx? α} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢ (.case a A B b c) : C) : D.case_splitRight ⊢ a : .coprod A B
  := match D with | .case _ da _ _ => da

def Deriv.case_left {Γ : Ctx? α} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢ (.case a A B b c) : C) : D.case_splitLeft.cons ⟨A, ⊤⟩ ⊢ b : C
  := match D with | .case _ _ db _ => db

def Deriv.case_right {Γ : Ctx? α} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢ (.case a A B b c) : C) : D.case_splitLeft.cons ⟨B, ⊤⟩ ⊢ c : C
  := match D with | .case _ _ _ dc => dc

def Deriv.abort_arg {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢ (.abort A a) : A) : Γ ⊢ a : .empty
  := match D with | .abort da => da

def Deriv.iter_splitLeft {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.iter a A B b) : B) : Ctx? α
  := match D with | .iter (Γl := Γl) .. => Γl

def Deriv.iter_splitRight {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.iter a A B b) : B) : Ctx? α
  := match D with | .iter (Γr := Γr) .. => Γr

def Deriv.iter_split {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.iter a A B b) : B) : Γ.SSplit (D.iter_splitLeft) (D.iter_splitRight)
  := match D with | .iter dΓ _ _ _ _ => dΓ

theorem Deriv.iter_copy {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.iter a A B b) : B) : D.iter_splitLeft.copy
  := match D with | .iter _ hc _ _ _ => hc

theorem Deriv.iter_del {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.iter a A B b) : B) : D.iter_splitLeft.del
  := match D with | .iter _ _ hd _ _ => hd

def Deriv.iter_bind {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.iter a A B b) : B) : D.iter_splitRight ⊢ a : A
  := match D with | .iter _ _ _ da _ => da

def Deriv.iter_body {Γ : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢ (.iter a A B b) : B) : D.iter_splitLeft.cons ⟨A, ⊤⟩ ⊢ b : .coprod B A
  := match D with | .iter _ _ _ _ db => db

--TODO: want minimization for IsWt inversion...

end Term

end Refinery
