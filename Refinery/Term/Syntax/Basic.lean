import Discretion.Wk.Nat

namespace Refinery

scoped notation "↑ⁿ" => Nat.liftWk

universe u v

inductive Term (φ : Type u) (α : Type v) : Type (max u v)
  | bv (ix : Nat) : Term φ α
  | op (f : φ) (a : Term φ α) : Term φ α
  | let₁ (a : Term φ α) (A : α) (b : Term φ α) : Term φ α
  | let₂ (a : Term φ α) (A B : α) (b : Term φ α) : Term φ α
  | unit : Term φ α
  | pair (a : Term φ α) (b : Term φ α) : Term φ α
  | inl (A B : α) (a : Term φ α) : Term φ α
  | inr (A B : α) (b : Term φ α) : Term φ α
  | case (a : Term φ α) (A B : α) (b : Term φ α) (c : Term φ α) : Term φ α
  | abort (A : α) (a : Term φ α) : Term φ α
  | iter (a : Term φ α) (A B : α) (b : Term φ α) : Term φ α
  | invalid : Term φ α

namespace Term

variable {φ : Type u} {α : Type v}

@[simp]
def ren (ρ : ℕ → ℕ) : Term φ α → Term φ α
  | .bv ix => .bv (ρ ix)
  | .op f a => .op f (ren ρ a)
  | .let₁ a A b => .let₁ (ren ρ a) A (ren (↑ⁿ ρ) b)
  | .let₂ a A B b => .let₂ (ren ρ a) A B (ren (↑ⁿ (↑ⁿ ρ)) b)
  | .unit => .unit
  | .pair a b => .pair (ren ρ a) (ren ρ b)
  | .inl A B a => .inl A B (ren ρ a)
  | .inr A B b => .inr A B (ren ρ b)
  | .case a A B b c => .case (ren ρ a) A B (ren (↑ⁿ ρ) b) (ren (↑ⁿ ρ) c)
  | .abort A a => .abort A (ren ρ a)
  | .iter a A B b => .iter (ren ρ a) A B (ren (↑ⁿ ρ) b)
  | .invalid => .invalid

@[simp] theorem ren_id (t : Term φ α) : t.ren id = t := by induction t <;> simp [*]

theorem ren_comp (ρ ρ' : ℕ → ℕ) (t : Term φ α) : t.ren (ρ ∘ ρ') = (t.ren ρ').ren ρ :=
  by induction t generalizing ρ ρ' <;> simp [Nat.liftWk_comp, *]

theorem ren_ren (ρ ρ' : ℕ → ℕ) (t : Term φ α) : (t.ren ρ').ren ρ = t.ren (ρ ∘ ρ')
  := (ren_comp ρ ρ' t).symm

scoped notation "↑⁰" => ren Nat.succ

scoped notation "↑¹" => ren (Nat.liftWk Nat.succ)

scoped notation "↑²" => ren (Nat.liftWk (Nat.liftWk Nat.succ))

def Subst (φ : Type u) (α : Type v) : Type _ := ℕ → Term φ α

def Subst.get (σ : Subst φ α) (ix : ℕ) : Term φ α := σ ix

@[ext] theorem Subst.ext (σ τ : Subst φ α) (h : ∀ ix, σ.get ix = τ.get ix) : σ = τ := funext h

instance Subst.instOne : One (Subst φ α) where
  one := λ i => .bv i

@[simp] theorem Subst.get_id (ix : ℕ) : (1 : Subst φ α).get ix = .bv ix := rfl

def Subst.lift (σ : Subst φ α) : Subst φ α
  | 0 => .bv 0
  | ix + 1 => ↑⁰ (σ ix)

@[simp] theorem Subst.get_lift_zero (σ : Subst φ α) : σ.lift.get 0 = .bv 0 := rfl

@[simp]
theorem Subst.get_lift_succ (σ : Subst φ α) (ix : ℕ) : σ.lift.get (ix + 1) = ↑⁰ (σ.get ix) := rfl

@[simp] theorem Subst.lift_id : (1 : Subst φ α).lift = 1 := by ext ix; cases ix <;> rfl

scoped notation "↑ˢ" => Subst.lift

@[simp]
def subst (σ : Subst φ α) : Term φ α → Term φ α
  | .bv ix => σ.get ix
  | .op f a => .op f (subst σ a)
  | .let₁ a A b => .let₁ (subst σ a) A (subst (↑ˢ σ) b)
  | .let₂ a A B b => .let₂ (subst σ a) A B (subst (↑ˢ (↑ˢ σ)) b)
  | .unit => .unit
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .inl A B a => .inl A B (subst σ a)
  | .inr A B a => .inr A B (subst σ a)
  | .case a A B b c => .case (subst σ a) A B (subst (↑ˢ σ) b) (subst (↑ˢ σ) c)
  | .abort A a => .abort A (subst σ a)
  | .iter a A B b => .iter (subst σ a) A B (subst (↑ˢ σ) b)
  | .invalid => .invalid
  --TODO: metavariables?

instance instSMul : SMul (Subst φ α) (Term φ α) where
  smul := subst

instance Subst.instMul : Mul (Subst φ α) where
  mul σ τ i := (τ.get i).subst σ

@[simp] theorem subst_id (t : Term φ α) : t.subst 1 = t := by induction t <;> simp [subst, *]

@[simp] theorem smul_id (t : Term φ α) : (1 : Subst φ α) • t = t := subst_id t

def Subst.comp (σ τ : Subst φ α) : Subst φ α := λ ix => (τ.get ix).subst σ

@[simp]
theorem Subst.comp_get (σ τ : Subst φ α) (ix : ℕ) : (σ * τ).get ix = (τ.get ix).subst σ := rfl

@[simp] theorem Subst.comp_id (σ : Subst φ α) : σ * 1 = σ := by ext ix; simp

@[simp] theorem Subst.id_comp (σ : Subst φ α) : 1 * σ = σ := by ext ix; simp

def Subst.renIn (ρ : ℕ → ℕ) (σ : Subst φ α) : Subst φ α := λ ix => σ.get (ρ ix)

@[simp]
theorem Subst.get_renIn (ρ : ℕ → ℕ) (σ : Subst φ α) (ix : ℕ) : (σ.renIn ρ).get ix = σ.get (ρ ix)
  := rfl

def Subst.renOut (σ : Subst φ α) (ρ : ℕ → ℕ) : Subst φ α := λ ix => (σ.get ix).ren ρ

@[simp]
theorem Subst.get_renOut (σ : Subst φ α) (ρ : ℕ → ℕ) (ix : ℕ) : (σ.renOut ρ).get ix = (σ.get ix).ren ρ
  := rfl

def Subst.ofRen (ρ : ℕ → ℕ) : Subst φ α := λ ix => .bv (ρ ix)

@[simp]
theorem Subst.get_ofRen (ρ : ℕ → ℕ) (ix : ℕ)
  : (Subst.ofRen (φ := φ) (α := α) ρ).get ix = .bv (ρ ix) := rfl

instance Subst.coeRen : Coe (ℕ → ℕ) (Subst φ α) where
  coe := ofRen

@[simp]
theorem Subst.coe_eq_coe (ρ σ : ℕ → ℕ) : (ρ : Subst φ α) = (σ : Subst φ α) ↔ ρ = σ
  := by constructor
        intro h; ext i; have h := congrFun h i; convert h using 0; simp [ofRen]
        intro h; cases h; rfl

theorem Subst.lift_renIn (σ : Subst φ α) (ρ : ℕ → ℕ)
  : (σ.renIn ρ).lift = σ.lift.renIn (↑ⁿ ρ) := by ext i; cases i <;> rfl

theorem Subst.lift_renOut (σ : Subst φ α) (ρ : ℕ → ℕ)
  : (σ.renOut ρ).lift = (σ.lift).renOut (↑ⁿ ρ)
  := by ext i; cases i <;> simp [ren_ren, Nat.liftWk_comp_succ]

theorem subst_renIn {σ : Subst φ α} {ρ : ℕ → ℕ} {a : Term φ α}
  : a.subst (σ.renIn ρ) = (a.ren ρ).subst σ
  := by induction a generalizing σ ρ <;> simp [Subst.lift_renIn, *]

theorem subst_renOut {σ : Subst φ α} {ρ : ℕ → ℕ} {a : Term φ α}
  : a.subst (σ.renOut ρ) = (a.subst σ).ren ρ
  := by induction a generalizing σ ρ <;> simp [Subst.lift_renOut, *]

theorem renIn_succ_lift {σ : Subst φ α} : σ.lift.renIn .succ = σ.renOut .succ
  := by ext i; cases i <;> simp

theorem Subst.lift_comp (σ τ : Subst φ α) : (σ * τ).lift = σ.lift * τ.lift := by
  ext i; cases i <;> simp [<-subst_renOut, <-subst_renIn, renIn_succ_lift]

theorem subst_comp {σ τ : Subst φ α} {a : Term φ α} : a.subst (σ * τ) = (a.subst τ).subst σ
  := by induction a generalizing σ τ <;> simp [Subst.lift_comp, *]

theorem subst_subst {σ τ : Subst φ α} {a : Term φ α} : (a.subst τ).subst σ = a.subst (σ * τ)
  := subst_comp.symm

theorem Subst.comp_assoc (σ τ ρ : Subst φ α) : (σ * τ) * ρ = σ * (τ * ρ) := by
  ext i; simp [subst_comp]

instance Subst.instMonoid : Monoid (Subst φ α) where
  one_mul := Subst.id_comp
  mul_one := Subst.comp_id
  mul_assoc := Subst.comp_assoc

instance instMulAction : MulAction (Subst φ α) (Term φ α) where
  one_smul := smul_id
  mul_smul _ _ _ := subst_comp

end Term
