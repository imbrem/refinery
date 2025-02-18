import Discretion.Wk.Nat

namespace Refinery

scoped notation "↑ⁿ" => Nat.liftWk

universe u

inductive Term (φ : Type u) : Type u
  | bv (ix : Nat) : Term φ
  | op (f : φ) (a : Term φ) : Term φ
  | let₁ (a : Term φ) (b : Term φ) : Term φ
  | let₂ (a : Term φ) (b : Term φ) : Term φ
  | unit : Term φ
  | pair (a : Term φ) (b : Term φ) : Term φ
  | inl (a : Term φ) : Term φ
  | inr (a : Term φ) : Term φ
  | case (a : Term φ) (b : Term φ) (c : Term φ) : Term φ
  | abort (a : Term φ) : Term φ
  | iter (a : Term φ) (b : Term φ) : Term φ
  | invalid : Term φ

namespace Term

variable {φ : Type u}

@[simp]
def ren (ρ : ℕ → ℕ) : Term φ → Term φ
  | .bv ix => .bv (ρ ix)
  | .op f a => .op f (ren ρ a)
  | .let₁ a b => .let₁ (ren ρ a) (ren (↑ⁿ ρ) b)
  | .let₂ a b => .let₂ (ren ρ a) (ren (↑ⁿ (↑ⁿ ρ)) b)
  | .unit => .unit
  | .pair a b => .pair (ren ρ a) (ren ρ b)
  | .inl a => .inl (ren ρ a)
  | .inr a => .inr (ren ρ a)
  | .case a b c => .case (ren ρ a) (ren (↑ⁿ ρ) b) (ren (↑ⁿ ρ) c)
  | .abort a => .abort (ren ρ a)
  | .iter a b => .iter (ren ρ a) (ren (↑ⁿ ρ) b)
  | .invalid => .invalid

@[simp] theorem ren_id (t : Term φ) : t.ren id = t := by induction t <;> simp [*]

theorem ren_comp (ρ ρ' : ℕ → ℕ) (t : Term φ) : t.ren (ρ ∘ ρ') = (t.ren ρ').ren ρ :=
  by induction t generalizing ρ ρ' <;> simp [Nat.liftWk_comp, *]

theorem ren_ren (ρ ρ' : ℕ → ℕ) (t : Term φ) : (t.ren ρ').ren ρ = t.ren (ρ ∘ ρ')
  := (ren_comp ρ ρ' t).symm

scoped notation "↑⁰" => ren Nat.succ

def Subst (φ : Type u) : Type u := ℕ → Term φ

def Subst.get (σ : Subst φ) (ix : ℕ) : Term φ := σ ix

@[ext] theorem Subst.ext (σ τ : Subst φ) (h : ∀ ix, σ.get ix = τ.get ix) : σ = τ := funext h

instance Subst.instOne : One (Subst φ) where
  one := λ i => .bv i

@[simp] theorem Subst.get_id (ix : ℕ) : (1 : Subst φ).get ix = .bv ix := rfl

def Subst.lift (σ : Subst φ) : Subst φ
  | 0 => .bv 0
  | ix + 1 => ↑⁰ (σ ix)

@[simp] theorem Subst.get_lift_zero (σ : Subst φ) : σ.lift.get 0 = .bv 0 := rfl

@[simp]
theorem Subst.get_lift_succ (σ : Subst φ) (ix : ℕ) : σ.lift.get (ix + 1) = ↑⁰ (σ.get ix) := rfl

@[simp] theorem Subst.lift_id : (1 : Subst φ).lift = 1 := by ext ix; cases ix <;> rfl

scoped notation "↑ˢ" => Subst.lift

@[simp]
def subst (σ : Subst φ) : Term φ → Term φ
  | .bv ix => σ.get ix
  | .op f a => .op f (subst σ a)
  | .let₁ a b => .let₁ (subst σ a) (subst (↑ˢ σ) b)
  | .let₂ a b => .let₂ (subst σ a) (subst (↑ˢ (↑ˢ σ)) b)
  | .unit => .unit
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .inl a => .inl (subst σ a)
  | .inr a => .inr (subst σ a)
  | .case a b c => .case (subst σ a) (subst (↑ˢ σ) b) (subst (↑ˢ σ) c)
  | .abort a => .abort (subst σ a)
  | .iter a b => .iter (subst σ a) (subst (↑ˢ σ) b)
  | .invalid => .invalid

instance instSMul : SMul (Subst φ) (Term φ) where
  smul := subst

instance Subst.instMul : Mul (Subst φ) where
  mul σ τ i := (τ.get i).subst σ

@[simp] theorem subst_id (t : Term φ) : t.subst 1 = t := by induction t <;> simp [subst, *]

@[simp] theorem smul_id (t : Term φ) : (1 : Subst φ) • t = t := subst_id t

def Subst.comp (σ τ : Subst φ) : Subst φ := λ ix => (τ.get ix).subst σ

@[simp]
theorem Subst.comp_get (σ τ : Subst φ) (ix : ℕ) : (σ * τ).get ix = (τ.get ix).subst σ := rfl

@[simp] theorem Subst.comp_id (σ : Subst φ) : σ * 1 = σ := by ext ix; simp

@[simp] theorem Subst.id_comp (σ : Subst φ) : 1 * σ = σ := by ext ix; simp

def Subst.renIn (ρ : ℕ → ℕ) (σ : Subst φ) : Subst φ := λ ix => σ.get (ρ ix)

@[simp]
theorem Subst.get_renIn (ρ : ℕ → ℕ) (σ : Subst φ) (ix : ℕ) : (σ.renIn ρ).get ix = σ.get (ρ ix)
  := rfl

def Subst.renOut (σ : Subst φ) (ρ : ℕ → ℕ) : Subst φ := λ ix => (σ.get ix).ren ρ

@[simp]
theorem Subst.get_renOut (σ : Subst φ) (ρ : ℕ → ℕ) (ix : ℕ) : (σ.renOut ρ).get ix = (σ.get ix).ren ρ
  := rfl

def Subst.ofRen (ρ : ℕ → ℕ) : Subst φ := λ ix => .bv (ρ ix)

@[simp]
theorem Subst.get_ofRen (ρ : ℕ → ℕ) (ix : ℕ) : (Subst.ofRen (φ := φ) ρ).get ix = .bv (ρ ix) := rfl

instance Subst.coeRen : Coe (ℕ → ℕ) (Subst φ) where
  coe := ofRen

@[simp]
theorem Subst.coe_eq_coe (ρ σ : ℕ → ℕ) : (ρ : Subst φ) = (σ : Subst φ) ↔ ρ = σ
  := by constructor
        intro h; ext i; have h := congrFun h i; convert h using 0; simp [ofRen]
        intro h; cases h; rfl

theorem Subst.lift_renIn (σ : Subst φ) (ρ : ℕ → ℕ)
  : (σ.renIn ρ).lift = σ.lift.renIn (↑ⁿ ρ) := by ext i; cases i <;> rfl

theorem Subst.lift_renOut (σ : Subst φ) (ρ : ℕ → ℕ)
  : (σ.renOut ρ).lift = (σ.lift).renOut (↑ⁿ ρ)
  := by ext i; cases i <;> simp [ren_ren, Nat.liftWk_comp_succ]

theorem subst_renIn {σ : Subst φ} {ρ : ℕ → ℕ} {a : Term φ}
  : a.subst (σ.renIn ρ) = (a.ren ρ).subst σ
  := by induction a generalizing σ ρ <;> simp [Subst.lift_renIn, *]

theorem subst_renOut {σ : Subst φ} {ρ : ℕ → ℕ} {a : Term φ}
  : a.subst (σ.renOut ρ) = (a.subst σ).ren ρ
  := by induction a generalizing σ ρ <;> simp [Subst.lift_renOut, *]

theorem renIn_succ_lift {σ : Subst φ} : σ.lift.renIn .succ = σ.renOut .succ
  := by ext i; cases i <;> simp

theorem Subst.lift_comp (σ τ : Subst φ) : (σ * τ).lift = σ.lift * τ.lift := by
  ext i; cases i <;> simp [<-subst_renOut, <-subst_renIn, renIn_succ_lift]

theorem subst_comp {σ τ : Subst φ} {a : Term φ} : a.subst (σ * τ) = (a.subst τ).subst σ
  := by induction a generalizing σ τ <;> simp [Subst.lift_comp, *]

theorem subst_subst {σ τ : Subst φ} {a : Term φ} : (a.subst τ).subst σ = a.subst (σ * τ)
  := subst_comp.symm

theorem Subst.comp_assoc (σ τ ρ : Subst φ) : (σ * τ) * ρ = σ * (τ * ρ) := by
  ext i; simp [subst_comp]

instance Subst.instMonoid : Monoid (Subst φ) where
  one_mul := Subst.id_comp
  mul_one := Subst.comp_id
  mul_assoc := Subst.comp_assoc

instance instMulAction : MulAction (Subst φ) (Term φ) where
  one_smul := smul_id
  mul_smul _ _ _ := subst_comp

end Term
