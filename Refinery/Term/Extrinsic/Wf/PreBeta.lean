import Refinery.Term.Extrinsic.Refinement.Wk.Relation
import Refinery.Term.Extrinsic.Wf.Wk

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term


variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α}

theorem Wf.pre_beta_pos  {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, q⟩) B)
    {el er} [ha : HasEff el a.tm] [hb : HasEff er b.tm] (he : el ⇀ er) (heq : q ≤ (pquant el).pos)
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≤ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := by
    apply DRWS.uniform.base
    apply DRWS.refStep.beta
    apply DRWS.Beta.beta_pos <;> assumption

theorem Wf.pre_beta_neg {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, q⟩) B)
    {el er} [ha : HasEff el a.tm] [hb : HasEff er b.tm] (he : el ↽ er) (heq : q ≤ (pquant el).neg)
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≥ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := by
    apply DRWS.uniform.base
    apply DRWS.refStep.beta
    apply DRWS.Beta.beta_neg <;> assumption

theorem Wf.pre_beta {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, q⟩) B)
    {el er} [ha : HasEff el a.tm] [hb : HasEff er b.tm] (he : el ⇌ er) (heq : q ≤ (pquant el))
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := ⟨pre_beta_pos hΓ a q hq b he.left heq.left, pre_beta_neg hΓ a q hq b he.right heq.right⟩

theorem Wf.pre_beta_pureIn {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, q⟩) B)
    [ha : HasEff ⊥ a.tm]
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := pre_beta hΓ a q hq b (commutes_bot_left (r := ⊤)) (by simp [OrderedPQuant.pquant_bot])

theorem Wf.pre_beta_pureLin {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A)
    (b : Wf R (Γl.cons ⟨A, 1⟩) B)
    [ha : HasEff ⊥ a.tm]
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv 1 bot_le)
    := pre_beta_pureIn hΓ a 1 bot_le b

theorem Wf.pre_beta_pureLout {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A)
    (b : Wf R (Γl.cons ⟨A, 1⟩) B)
    [hb : HasEff ⊥ b.tm]
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv 1 bot_le)
    := pre_beta hΓ a 1 bot_le b (commutes_bot_right (l := ⊤)) bot_le
