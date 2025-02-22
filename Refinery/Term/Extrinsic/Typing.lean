import Refinery.Ctx.Basic
import Refinery.Ctx.SSplit
import Refinery.Signature
import Refinery.Term.Syntax

namespace Refinery

open HasQuant

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

--TODO: port to PSplit for hax?

inductive Deriv : ε → Ctx? α ε → Ty α → Term φ (Ty α) → Type _
  | bv {Γ} : Γ.At ⟨A, 1, e⟩ n → Deriv e Γ A (.bv n)
  | op {Γ e A B f a} : S.IsFn f e A B → Deriv e Γ A a → Deriv e Γ B (.op f a)
  | let₁ {Γ Γl Γr e A B a b} :
    Γ.SSplit Γl Γr →
    Deriv e Γr A a → Deriv e (Γl.cons ⟨A, ⊤, ⊥⟩) B b → Deriv e Γ B (.let₁ a A b)
  | unit {Γ} : Γ.del → Deriv e Γ .unit .unit
  | pair {Γ Γl Γr e A B a b} :
    Γ.SSplit Γl Γr →
    Deriv e Γl A a → Deriv e Γr B b → Deriv e Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr e A B C a b} :
    Γ.SSplit Γl Γr →
    Deriv e Γr (.tensor A B) a → Deriv e ((Γl.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩) C b
      → Deriv e Γ C (.let₂ a A B b)
  | inl {Γ e A B a} : Deriv e Γ A a → Deriv e Γ (.coprod A B) (.inl A B a)
  | inr {Γ e A B b} : Deriv e Γ B b → Deriv e Γ (.coprod A B) (.inr A B b)
  | case {Γ Γl Γr e A B C a b c} :
    Γ.SSplit Γl Γr →
    Deriv e Γr (.coprod A B) a → Deriv e (Γl.cons ⟨A, ⊤, ⊥⟩) C b → Deriv e (Γl.cons ⟨B, ⊤, ⊥⟩) C c
      → Deriv e Γ C (.case a A B b c)
  | abort {Γ e A a} : Deriv e Γ .empty a → Deriv e Γ A (.abort A a)
  | iter {Γ Γl Γr e A B a b} :
    Γ.SSplit Γl Γr →
    e ∈ S.iterative →
    Γl.copy → Γl.del →
    Deriv e Γr A a → Deriv e (Γl.cons ⟨A, ⊤, ⊥⟩) (.coprod B A) b → Deriv e Γ B (.iter a A B b)

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

def Deriv.cast {e e' : ε} {Γ Γ' : Ctx? α ε} {A A' : Ty α} {a a' : Term φ (Ty α)}
  (he : e = e') (hΓ : Γ = Γ') (hA : A = A') (ha : a = a')
  (D : Γ ⊢[e] a : A) : (Γ' ⊢[e'] a' : A') := he ▸ hΓ ▸ hA ▸ ha ▸ D

abbrev Deriv.cast_eff {e e' : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
  (he : e = e') (D : Γ ⊢[e] a : A) : Γ ⊢[e'] a : A := D.cast he rfl rfl rfl

abbrev Deriv.cast_ctx {e : ε} {Γ Γ' : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
  (hΓ : Γ = Γ') (D : Γ ⊢[e] a : A) : Γ' ⊢[e] a : A := D.cast rfl hΓ rfl rfl

abbrev Deriv.cast_ty {e : ε} {Γ : Ctx? α ε} {A A' : Ty α} {a : Term φ (Ty α)}
  (hA : A = A') (D : Γ ⊢[e] a : A) : Γ ⊢[e] a : A' := D.cast rfl rfl hA rfl

abbrev Deriv.cast_term {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a a' : Term φ (Ty α)}
  (ha : a = a') (D : Γ ⊢[e] a : A) : Γ ⊢[e] a' : A := D.cast rfl rfl rfl ha

def IsWt (e : ε) (Γ : Ctx? α ε) (A : Ty α) (a : Term φ (Ty α)) : Prop := Nonempty (Γ ⊢[e] a : A)

@[match_pattern]
theorem Deriv.wt {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢[e] a : A)
  : IsWt e Γ A a := ⟨D⟩

theorem IsWt.mono {e e' : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)} (he : e ≤ e')
  : IsWt e Γ A a → IsWt e' Γ A a := λ ⟨D⟩ => ⟨D.mono he⟩

theorem IsWt.top {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
  (D : IsWt e Γ A a) : IsWt ⊤ Γ A a := D.mono le_top

theorem Deriv.wt_top {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢[e] a : A)
  : IsWt ⊤ Γ A a := D.wt.top

theorem IsWt.exists_iff {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
  : (∃e, IsWt e Γ A a) ↔ IsWt ⊤ Γ A a := ⟨λ⟨_, h⟩ => h.top, λh => ⟨⊤, h⟩⟩

theorem Deriv.bv_at {e : ε} {Γ : Ctx? α ε} {A : Ty α} {n : ℕ} (D : Γ ⊢[e] (.bv (φ := φ) n) : A)
  : Γ.At ⟨A, 1, e⟩ n := match D with | .bv hv => hv

theorem IsWt.bv_at {e : ε} {Γ : Ctx? α ε} {A : Ty α} {n : ℕ} (D : IsWt (φ := φ) e Γ A (.bv n))
  : Γ.At ⟨A, 1, e⟩ n := D.elim Deriv.bv_at

theorem Deriv.op_fn {e : ε} {Γ : Ctx? α ε} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : Γ ⊢[e] (.op f a) : B) : S.IsFn f e (S.src f) B
  := match D with | .op hf da => by cases hf.src; exact hf

theorem IsWt.op_fn {e : ε} {Γ : Ctx? α ε} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : IsWt e Γ B (.op f a)) : S.IsFn f e (S.src f) B := D.elim Deriv.op_fn

def Deriv.op_arg {e : ε} {Γ : Ctx? α ε} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : Γ ⊢[e] (.op f a) : B) : Γ ⊢[e] a : S.src f
  := match D with | .op hf da => da.cast_ty hf.src

theorem IsWt.op_arg {e : ε} {Γ : Ctx? α ε} {B : Ty α} {f : φ} {a : Term φ (Ty α)}
  (D : IsWt e Γ B (.op f a)) : IsWt e Γ (S.src f) a := ⟨(Classical.choice D).op_arg⟩

def Deriv.let₁_splitLeft {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₁ a A b) : B) : Ctx? α ε
  := match D with | .let₁ (Γl := Γl) .. => Γl

def Deriv.let₁_splitRight {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₁ a A b) : B) : Ctx? α ε
  := match D with | .let₁ (Γr := Γr) .. => Γr

def Deriv.let₁_split {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₁ a A b) : B) : Γ.SSplit (D.let₁_splitLeft) (D.let₁_splitRight)
  := match D with | .let₁ dΓ _ _ => dΓ

def Deriv.let₁_bind {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₁ a A b) : B) : D.let₁_splitRight ⊢[e] a : A
  := match D with | .let₁ _ da _ => da

def Deriv.let₁_expr {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₁ a A b) : B) : (D.let₁_splitLeft.cons ⟨A, ⊤, ⊥⟩) ⊢[e] b : B
  := match D with | .let₁ _ _ db => db

theorem Deriv.unit_wk {e : ε} {Γ : Ctx? α ε} {A : Ty α} (D : Γ ⊢[e] .unit (φ := φ) : A) : Γ.del
  := match D with | .unit dΓ => dΓ

theorem IsWt.unit_wk {e : ε} {Γ : Ctx? α ε} (D : IsWt (φ := φ) e Γ A .unit) : Γ.del
  := D.elim Deriv.unit_wk

def Deriv.pair_splitLeft {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.pair a b) : .tensor A B) : Ctx? α ε
  := match D with | .pair (Γl := Γl) .. => Γl

def Deriv.pair_splitRight {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.pair a b) : .tensor A B) : Ctx? α ε
  := match D with | .pair (Γr := Γr) .. => Γr

def Deriv.pair_split {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.pair a b) : .tensor A B) : Γ.SSplit (D.pair_splitLeft) (D.pair_splitRight)
  := match D with | .pair dΓ _ _ => dΓ

def Deriv.pair_left {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.pair a b) : .tensor A B) : D.pair_splitLeft ⊢[e] a : A
  := match D with | .pair _ da _ => da

def Deriv.pair_right {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.pair a b) : .tensor A B) : D.pair_splitRight ⊢[e] b : B
  := match D with | .pair _ _ db => db

def Deriv.let₂_splitLeft {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₂ a A B b) : C) : Ctx? α ε
  := match D with | .let₂ (Γl := Γl) .. => Γl

def Deriv.let₂_splitRight {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₂ a A B b) : C) : Ctx? α ε
  := match D with | .let₂ (Γr := Γr) .. => Γr

def Deriv.let₂_split {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₂ a A B b) : C) : Γ.SSplit (D.let₂_splitLeft) (D.let₂_splitRight)
  := match D with | .let₂ dΓ _ _ => dΓ

def Deriv.let₂_bind {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₂ a A B b) : C) : D.let₂_splitRight ⊢[e] a : .tensor A B
  := match D with | .let₂ _ da _ => da

def Deriv.let₂_expr {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.let₂ a A B b) : C) : (D.let₂_splitLeft.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩ ⊢[e] b : C
  := match D with | .let₂ _ _ db => db

def Deriv.inl_arg {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢[e] (.inl A B a) : .coprod A B) : Γ ⊢[e] a : A
  := match D with | .inl da => da

def Deriv.inr_arg {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.inr A B b) : .coprod A B) : Γ ⊢[e] b : B
  := match D with | .inr db => db

def Deriv.case_splitLeft {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢[e] (.case a A B b c) : C) : Ctx? α ε
  := match D with | .case (Γl := Γl) .. => Γl

def Deriv.case_splitRight {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢[e] (.case a A B b c) : C) : Ctx? α ε
  := match D with | .case (Γr := Γr) .. => Γr

def Deriv.case_bind {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢[e] (.case a A B b c) : C) : D.case_splitRight ⊢[e] a : .coprod A B
  := match D with | .case _ da _ _ => da

def Deriv.case_left {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢[e] (.case a A B b c) : C) : D.case_splitLeft.cons ⟨A, ⊤, ⊥⟩ ⊢[e] b : C
  := match D with | .case _ _ db _ => db

def Deriv.case_right {e : ε} {Γ : Ctx? α ε} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (D : Γ ⊢[e] (.case a A B b c) : C) : D.case_splitLeft.cons ⟨B, ⊤, ⊥⟩ ⊢[e] c : C
  := match D with | .case _ _ _ dc => dc

def Deriv.abort_arg {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢[e] (.abort A a) : A) : Γ ⊢[e] a : .empty
  := match D with | .abort da => da

def Deriv.iter_splitLeft {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : Ctx? α ε
  := match D with | .iter (Γl := Γl) .. => Γl

def Deriv.iter_splitRight {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : Ctx? α ε
  := match D with | .iter (Γr := Γr) .. => Γr

def Deriv.iter_split {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : Γ.SSplit (D.iter_splitLeft) (D.iter_splitRight)
  := match D with | .iter dΓ _ _ _ _ _ => dΓ

theorem Deriv.iter_eff {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : e ∈ S.iterative
  := match D with | .iter _ hei _ _ _ _ => hei

theorem IsWt.iter_eff {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : IsWt e Γ B (.iter a A B b)) : e ∈ S.iterative := D.elim Deriv.iter_eff

theorem Deriv.iter_copy {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : D.iter_splitLeft.copy
  := match D with | .iter _ _ hc _ _ _ => hc

theorem Deriv.iter_del {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : D.iter_splitLeft.del
  := match D with | .iter _ _ _ hd _ _ => hd

def Deriv.iter_bind {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : D.iter_splitRight ⊢[e] a : A
  := match D with | .iter _ _ _ _ da _ => da

def Deriv.iter_iter {e : ε} {Γ : Ctx? α ε} {A B : Ty α} {a b : Term φ (Ty α)}
  (D : Γ ⊢[e] (.iter a A B b) : B) : D.iter_splitLeft.cons ⟨A, ⊤, ⊥⟩ ⊢[e] b : .coprod B A
  := match D with | .iter _ _ _ _ _ db => db

--TODO: want minimization for IsWt inversion...

end Term

end Refinery
