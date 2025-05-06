import Refinery.Term.Extrinsic.Subst.Basic
import Refinery.Term.Extrinsic.Effect

namespace Refinery

namespace Term

open HasQuant HasPQuant HasCommRel

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

@[simp]
instance Deriv?.HasEff.top
  {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (D : Γ ⊢? a : v)
  : D.HasEff ⊤ := by cases D <;> infer_instance

@[simp]
instance Deriv?.HasEff.bv0
  {Γ : Ctx? α} {v : Var? α} : (Deriv?.bv0 (φ := φ) Γ v).HasEff e := by
  cases v using Var?.casesZero <;> simp [Deriv?.bv0, HasEff.bv]

theorem Deriv?.HasEff.wk
  {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {v : Var? α} {a : Term φ (Ty α)} (D : Δ ⊢? a : v)
  (h : quant Δ ≤ quant Γ) [hD : D.HasEff e] : (D.wk ρ h).HasEff e
  := by cases hD <;> constructor; infer_instance

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

instance SubstDS.HasEff.wkIn
  {Γ' Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff e] (ρ : Γ'.Wk Γ)
  : (σ.wkIn ρ).HasEff e := by
  induction hσ generalizing Γ' with
  | nil => simp [SubstDS.wkIn]
  | cons => constructor; infer_instance; apply Deriv?.HasEff.wk

instance SubstDS.HasEff.lift
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v) [h : σ.HasEff e] : (σ.lift v).HasEff e
  := by rw [SubstDS.lift]; infer_instance

inductive SubstDS.Pos : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
  | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : Pos e (.nil hΓ)
  | cons {e el er} {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
    (hσ : σ.Pos el) (ha : da.HasEff er)
    (hl : el ≤ e) (hr : er ≤ e) (hcomm : el ⇌ er) (hq: quant v ≤ (pquant er).pos)
    : Pos e (σ.cons hΓ da)

instance SubstDS.HasEff.pureTerm
  (e : ε) (a : Term φ (Ty α)) [ha : a.HasEff e] {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff ⊥] :
  (a.subst σ).HasEff e
  := by induction ha generalizing σ with
  | bv => sorry
  | iter => sorry
  | _ =>
    constructor <;>
    (try rw [<-SubstDS.lift_toSubst]) <;>
    sorry

attribute [class] SubstDS.Pos

attribute [simp, instance] SubstDS.Pos.nil

theorem SubstDS.Pos.mono
  {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (h : σ.Pos e)
  : σ.Pos e' := by
  induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm hq =>
    constructor; apply_assumption; assumption
    apply le_trans <;> assumption; apply le_trans <;> assumption; assumption
    assumption

instance SubstDS.Pos.has_eff
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [h : σ.Pos e]
  : σ.HasEff e := by induction h with
  | nil => constructor
  | cons =>
    constructor
    apply HasEff.mono (h := by assumption)
    assumption
    apply Deriv?.HasEff.mono (h := by assumption)
    assumption

theorem SubstDS.Pos.ssplit
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.Pos e ∧ (σ.ssplit hΔ).substRight.Pos e := by
  induction hσ generalizing Δl Δr with
  | nil => cases hΔ; simp [SubstDS.ssplit, SubstSSplit.erase_left]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ => rename Var? _ => v; cases hΔ with
  | cons hΔ hlr => cases hlr with
  | left  =>
    simp only [SubstDS.ssplit]
    if hv : v.used then
      rw [dite_cond_eq_true (by simp [hv])]
      constructor
      constructor <;> first | assumption | apply (Iσ _).left
      constructor
      apply (Iσ _).right
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; rfl
    else
      rw [dite_cond_eq_false (by simp [hv])]
      constructor
      constructor
      apply (Iσ _).left
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; apply le_top
      constructor
      apply (Iσ _).right
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; rfl
  | right =>
    constructor
    constructor
    apply (Iσ _).left
    simp [Deriv?.zero]
    assumption
    apply bot_le
    apply commutes_bot_right
    simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; rfl
    constructor
    apply (Iσ _).right
    all_goals assumption
  | sboth =>
    simp only [SubstDS.ssplit]
    if hv : v.used then
      rw [dite_cond_eq_true (by simp [hv])]
      constructor <;> constructor <;> first | assumption | apply (Iσ _).left | apply (Iσ _).right
    else
      rw [dite_cond_eq_false (by simp [hv])]
      simp only
      constructor
      constructor
      apply (Iσ _).left
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; apply le_top
      constructor
      apply (Iσ _).right
      all_goals assumption

instance SubstDS.Pos.ssplit_substLeft
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.Pos e := (Pos.ssplit σ hΔ).left

instance SubstDS.Pos.ssplit_substRight
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substRight.Pos e := (Pos.ssplit σ hΔ).right

instance SubstDS.Pos.wkIn
  {Γ' Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] (ρ : Γ'.Wk Γ)
  : (σ.wkIn ρ).Pos e := by
  induction hσ generalizing Γ' with
  | nil => simp [SubstDS.wkIn]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i e el er Γ Γl Γr Δ
    constructor
    apply_assumption
    apply Deriv?.HasEff.wk (e := er)
    all_goals assumption

instance SubstDS.Pos.lift
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v) [h : σ.Pos e] : (σ.lift v).Pos e
  := by
    rw [SubstDS.lift]; apply Pos.cons (er := ⊥); apply Pos.wkIn (e := e)
    infer_instance
    rfl
    apply bot_le
    apply commutes_bot_right
    rw [OrderedPQuant.pquant_bot]; apply le_top

instance SubstDS.Pos.refl {Γ : Ctx? α} : Pos (S := S) e (SubstDS.refl Γ)
  := by induction Γ <;> simp only [SubstDS.refl] <;> infer_instance

inductive SubstDS.Neg : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
  | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : Neg e (.nil hΓ)
  | cons {e el er} {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
    (hσ : σ.Neg el) (ha : da.HasEff er)
    (hl : el ≤ e) (hr : er ≤ e) (hcomm : el ⇌ er) (hq: quant v ≤ (pquant er).neg)
    : Neg e (σ.cons hΓ da)

attribute [class] SubstDS.Neg

attribute [simp, instance] SubstDS.Neg.nil

theorem SubstDS.Neg.mono
  {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (h : σ.Neg e)
  : σ.Neg e' := by
  induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm hq =>
    constructor; apply_assumption; assumption
    apply le_trans <;> assumption; apply le_trans <;> assumption; assumption
    assumption

instance SubstDS.Neg.has_eff
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [h : σ.Neg e]
  : σ.HasEff e := by induction h with
  | nil => constructor
  | cons =>
    constructor
    apply HasEff.mono (h := by assumption)
    assumption
    apply Deriv?.HasEff.mono (h := by assumption)
    assumption

theorem SubstDS.Neg.ssplit
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.Neg e ∧ (σ.ssplit hΔ).substRight.Neg e := by
  induction hσ generalizing Δl Δr with
  | nil => cases hΔ; simp [SubstDS.ssplit, SubstSSplit.erase_left]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ => rename Var? _ => v; cases hΔ with
  | cons hΔ hlr => cases hlr with
  | left  =>
    simp only [SubstDS.ssplit]
    if hv : v.used then
      rw [dite_cond_eq_true (by simp [hv])]
      constructor
      constructor <;> first | assumption | apply (Iσ _).left
      constructor
      apply (Iσ _).right
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; rfl
    else
      rw [dite_cond_eq_false (by simp [hv])]
      constructor
      constructor
      apply (Iσ _).left
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; apply le_top
      constructor
      apply (Iσ _).right
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; rfl
  | right =>
    constructor
    constructor
    apply (Iσ _).left
    simp [Deriv?.zero]
    assumption
    apply bot_le
    apply commutes_bot_right
    simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; rfl
    constructor
    apply (Iσ _).right
    all_goals assumption
  | sboth =>
    simp only [SubstDS.ssplit]
    if hv : v.used then
      rw [dite_cond_eq_true (by simp [hv])]
      constructor <;> constructor <;> first | assumption | apply (Iσ _).left | apply (Iσ _).right
    else
      rw [dite_cond_eq_false (by simp [hv])]
      simp only
      constructor
      constructor
      apply (Iσ _).left
      simp [Deriv?.zero]
      assumption
      apply bot_le
      apply commutes_bot_right
      simp only [Var?.unused.quant_top, top_le_iff, OrderedPQuant.pquant_bot]; apply le_top
      constructor
      apply (Iσ _).right
      all_goals assumption

instance SubstDS.Neg.ssplit_substLeft
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.Neg e := (Neg.ssplit σ hΔ).left

instance SubstDS.Neg.ssplit_substRight
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substRight.Neg e := (Neg.ssplit σ hΔ).right

instance SubstDS.Neg.wkIn
  {Γ' Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] (ρ : Γ'.Wk Γ)
  : (σ.wkIn ρ).Neg e := by
  induction hσ generalizing Γ' with
  | nil => simp [SubstDS.wkIn, Neg.nil]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i e el er Γ Γl Γr Δ
    constructor
    apply_assumption
    apply Deriv?.HasEff.wk (e := er)
    all_goals assumption

instance SubstDS.Neg.lift
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v) [h : σ.Neg e] : (σ.lift v).Neg e
  := by
  rw [SubstDS.lift]; apply Neg.cons (er := ⊥); apply Neg.wkIn (e := e)
  infer_instance
  rfl
  apply bot_le
  apply commutes_bot_right
  rw [OrderedPQuant.pquant_bot]; apply le_top

instance SubstDS.Neg.refl {Γ : Ctx? α} : Neg (S := S) e (SubstDS.refl Γ)
  := by induction Γ <;> simp only [SubstDS.refl] <;> infer_instance

class SubstDS.HasPos {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) : Prop where
  pos : ∃e, σ.Pos e

theorem SubstDS.Pos.has_pos {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [h : σ.Pos e] : σ.HasPos := ⟨⟨e, h⟩⟩

instance SubstDS.HasPos.nil {Γ : Ctx? α} {hΓ : Γ.del} : HasPos (.nil hΓ) := ⟨⊥, Pos.nil hΓ⟩

instance SubstDS.HasPos.ssplit_substLeft
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasPos] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.HasPos := have ⟨e, h⟩ := hσ; ⟨e, h.ssplit_substLeft σ hΔ⟩

instance SubstDS.HasPos.ssplit_substRight
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasPos] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substRight.HasPos := have ⟨e, h⟩ := hσ; ⟨e, h.ssplit_substRight σ hΔ⟩

instance SubstDS.HasPos.wkIn {Γ' Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasPos] (ρ : Γ'.Wk Γ)
  : (σ.wkIn ρ).HasPos := have ⟨_, h⟩ := hσ; ⟨_, h.wkIn σ ρ⟩

instance SubstDS.HasPos.lift {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v) [h : σ.HasPos]
  : (σ.lift v).HasPos := have ⟨_, h⟩ := h; ⟨_, h.lift _ _ _⟩

class SubstDS.HasNeg {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) : Prop where
  neg : ∃e, σ.Neg e

instance SubstDS.HasNeg.nil {Γ : Ctx? α} {hΓ : Γ.del} : HasNeg (.nil hΓ) := ⟨⊥, Neg.nil hΓ⟩

instance SubstDS.HasNeg.ssplit_substLeft
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasNeg] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.HasNeg := have ⟨e, h⟩ := hσ; ⟨e, h.ssplit_substLeft σ hΔ⟩

instance SubstDS.HasNeg.ssplit_substRight
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasNeg] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substRight.HasNeg := have ⟨e, h⟩ := hσ; ⟨e, h.ssplit_substRight σ hΔ⟩

instance SubstDS.HasNeg.wkIn {Γ' Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasNeg] (ρ : Γ'.Wk Γ)
  : (σ.wkIn ρ).HasNeg := have ⟨_, h⟩ := hσ; ⟨_, h.wkIn σ ρ⟩

instance SubstDS.HasNeg.lift {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v) [h : σ.HasNeg]
  : (σ.lift v).HasNeg := have ⟨_, h⟩ := h; ⟨_, h.lift _ _ _⟩

theorem SubstDS.Neg.has_neg {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [h : σ.Neg e] : σ.HasNeg := ⟨⟨e, h⟩⟩

class SubstDS.Bivalid {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) : Prop extends σ.HasPos, σ.HasNeg

instance SubstDS.Bivalid.nil {Γ : Ctx? α} {hΓ : Γ.del} : Bivalid (.nil hΓ) := ⟨⟩

instance SubstDS.Bivalid.wkIn {Γ' Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Bivalid] (ρ : Γ'.Wk Γ)
  : (σ.wkIn ρ).Bivalid := ⟨⟩

instance SubstDS.Bivalid.lift {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v) [h : σ.Bivalid]
  : (σ.lift v).Bivalid := ⟨⟩

-- inductive SubstDS.Bidir : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
--   | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : Bidir e (.nil hΓ)
--   | cons {e el er} {Γ Γl Γr Δ : Ctx? α}
--     (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
--     (hσ : σ.Pos el) (ha : da.HasEff er)
--     (hl : el ≤ e) (hr : er ≤ e) (hcomm : el ⇌ er) (hq: quant v ≤ pquant er)
--     : Bidir e (σ.cons hΓ da)

-- attribute [class] SubstDS.Bidir

-- theorem SubstDS.Bidir.mono
--   {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (h : σ.Bidir e)
--   : σ.Bidir e' := by
--   induction h with
--   | nil => constructor
--   | cons hΓ σ da hσ ha hl hr hcomm hq =>
--     constructor; apply_assumption; assumption
--     apply le_trans <;> assumption; apply le_trans <;> assumption; assumption
--     assumption
