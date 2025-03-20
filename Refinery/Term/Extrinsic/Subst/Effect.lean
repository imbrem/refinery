import Refinery.Term.Extrinsic.Subst.Basic
import Refinery.Term.Extrinsic.Effect

namespace Refinery

namespace Term

open HasQuant

open HasCommRel

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive Deriv?.HasEff
  : (e : ε) → {Γ : Ctx? α} → {v : Var? α} → {a : Term φ (Ty α)} → (Deriv? Γ v a) → Prop
  | valid
    {Γ : Ctx? α} {A} {q : Quant}
    {a : Term φ (Ty α)} (D : Γ ⊢ a : A) (hΓ : quant (Var?.mk A q) ≤ quant Γ)
    (ha : a.HasEff e) : HasEff e (.valid A q D hΓ)
  | zero {Γ : Ctx? α} (hΓ : Γ.del) (a A) : HasEff e (.zero hΓ a A)

attribute [class] Deriv?.HasEff

@[simp]
instance Deriv?.HasEff.instValid
    {Γ : Ctx? α} {A} {q : Quant}
    {a : Term φ (Ty α)} {D : Γ ⊢ a : A} {hΓ : quant (Var?.mk A q) ≤ quant Γ}
    [ha : a.HasEff e]
    : HasEff e (.valid A q D hΓ) := HasEff.valid D hΓ ha

@[simp]
instance Deriv?.HasEff.instZero {Γ : Ctx? α} [hΓ : Γ.del] {a A}
  : HasEff e (.zero hΓ a A) := HasEff.zero hΓ a A

@[simp]
instance Deriv?.HasEff.instUnused {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)}
  {hv : v.unused} [hΓ : Γ.del] : HasEff e (Deriv?.unused hΓ a hv) := by
  cases v using Var?.casesZero with
  | zero => simp [unused]
  | rest => simp at hv

theorem Deriv?.HasEff.mono
  {e e' : ε} (he : e ≤ e') {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (D : Γ ⊢? a : v)
  (h : D.HasEff e) : D.HasEff e' := by cases h with
  | valid => constructor; apply Term.HasEff.mono <;> assumption
  | zero => constructor

instance Deriv?.HasEff.top
  {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (D : Γ ⊢? a : v)
  : D.HasEff ⊤ := by cases D <;> infer_instance

inductive SubstDS.HasEff : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
  | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : HasEff e (.nil hΓ)
  | cons {e} {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
    (hσ : σ.HasEff e) (ha : da.HasEff e)
    : HasEff e (σ.cons hΓ da)

attribute [class] SubstDS.HasEff

@[simp]
instance SubstDS.HasEff.instNil {Γ : Ctx? α} [hΓ : Γ.del] : HasEff e (.nil hΓ) := HasEff.nil hΓ

@[simp]
instance SubstDS.HasEff.instCons {Γ Γl Γr Δ : Ctx? α} {da : Γr ⊢? a : v} {hΓ : Γ.SSplit Γl Γr}
  {σ : SubstDS φ Γl Δ} [hσ : σ.HasEff e] [ha : da.HasEff e]
  : HasEff e (σ.cons hΓ da) := HasEff.cons hΓ σ da hσ ha

theorem SubstDS.has_eff_head {Γ Γl Γr Δ : Ctx? α}
  (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v) (hΓ : Γ.SSplit Γl Γr) [hσ : (σ.cons hΓ da).HasEff e]
  : da.HasEff e := by cases hσ; assumption

theorem SubstDS.has_eff_tail {Γ Γl Γr Δ : Ctx? α}
  (σ : SubstDS φ Γl Δ)  (da : Γr ⊢? a : v) (hΓ : Γ.SSplit Γl Γr) [hσ : (σ.cons hΓ da).HasEff e]
  : σ.HasEff e := by cases hσ; assumption

theorem SubstDS.has_eff_cons {Γ Γl Γr Δ : Ctx? α}
  (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v) (hΓ : Γ.SSplit Γl Γr) [hσ : σ.HasEff e] [ha : da.HasEff e]
  : (σ.cons hΓ da).HasEff e := hσ.cons hΓ σ da ha

theorem SubstDS.has_eff_cons_iff {Γ Γl Γr Δ : Ctx? α}
  (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v) (hΓ : Γ.SSplit Γl Γr)
  : (σ.cons hΓ da).HasEff e ↔ σ.HasEff e ∧ da.HasEff e
  := ⟨λ _ => ⟨σ.has_eff_tail da hΓ, σ.has_eff_head da hΓ⟩, λ ⟨_, _⟩ => σ.has_eff_cons da hΓ⟩

theorem SubstDS.HasEff.cons_tail {Γ Γl Γr Δ : Ctx? α} {da : Γr ⊢? a : v} {hΓ : Γ.SSplit Γl Γr}
  {σ : SubstDS φ Γl Δ} (h : HasEff e (σ.cons hΓ da)) : σ.HasEff e := by cases h; assumption

theorem SubstDS.HasEff.cons_head {Γ Γl Γr Δ : Ctx? α} {da : Γr ⊢? a : v} {hΓ : Γ.SSplit Γl Γr}
  {σ : SubstDS φ Γl Δ} (h : HasEff e (σ.cons hΓ da)) : da.HasEff e := by cases h; assumption

theorem SubstDS.HasEff.cons_iff {Γ Γl Γr Δ : Ctx? α} {da : Γr ⊢? a : v} {hΓ : Γ.SSplit Γl Γr}
  {σ : SubstDS φ Γl Δ} : HasEff e (σ.cons hΓ da) ↔ σ.HasEff e ∧ da.HasEff e
  := σ.has_eff_cons_iff da hΓ

theorem SubstDS.HasEff.mono
  {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (h : σ.HasEff e)
  : σ.HasEff e' := by
  induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha =>
    constructor; apply_assumption; assumption; apply Deriv?.HasEff.mono <;> assumption

instance SubstDS.HasEff.top
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ)
  : σ.HasEff ⊤ := by induction σ <;> infer_instance

theorem SubstDS.HasEff.ssplit
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff e] (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.HasEff e ∧ (σ.ssplit hΔ).substRight.HasEff e := by
  induction hσ generalizing Δl Δr with
  | nil => cases hΔ; simp [SubstDS.ssplit, SubstSSplit.erase_left]
  | cons hΓ σ da hσ ha Iσ => rename Var? _ => v; cases hΔ with
  | cons hΔ hlr => cases hlr with
  | left =>
    simp only [SubstDS.ssplit]
    if hv : v.used then
      rw [dite_cond_eq_true (by simp [hv])]
      simp [HasEff.cons_iff, *]
    else
      rw [dite_cond_eq_false (by simp [hv])]
      simp [HasEff.cons_iff, *]
  | right =>
    simp [SubstDS.ssplit, HasEff.cons_iff, *]
  | sboth =>
    simp only [SubstDS.ssplit]
    if hv : v.used then
      rw [dite_cond_eq_true (by simp [hv])]
      simp [HasEff.cons_iff, *]
    else
      rw [dite_cond_eq_false (by simp [hv])]
      simp [HasEff.cons_iff, *]

instance SubstDS.HasEff.ssplit_substLeft
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.HasEff e := (HasEff.ssplit σ hΔ).left

instance SubstDS.HasEff.ssplit_substRight
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substRight.HasEff e := (HasEff.ssplit σ hΔ).right

inductive SubstDS.IsValid : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
  | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : IsValid e (.nil hΓ)
  | cons {e el er} {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
    (hσ : σ.IsValid el) (ha : da.HasEff er)
    (hl : el ≤ e) (hr : er ≤ e) (hcomm : el ⇌ er)
    : IsValid e (σ.cons hΓ da)

attribute [class] SubstDS.IsValid

theorem SubstDS.IsValid.mono
  {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (h : σ.IsValid e)
  : σ.IsValid e' := by
  induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm =>
    constructor; apply_assumption; assumption
    apply le_trans <;> assumption; apply le_trans <;> assumption; assumption

instance SubstDS.IsValid.has_eff
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [h : σ.IsValid e]
  : σ.HasEff e := by induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm Iσ => constructor; exact Iσ.mono hl; exact ha.mono hr
