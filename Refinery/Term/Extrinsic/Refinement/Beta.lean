import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Subst.Basic

open HasQuant

open HasPQuant

open HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive DRWS.Beta : DRWS φ α
  | elim_pos {Γ Γr : Ctx? α} {B : Ty α} {a b : Term φ (Ty α)}
    (hΓ : Γ.SSplit Γ Γr) (da : Γr ⊢ a : Ty.unit) (db : Γ.cons ⟨Ty.unit, ⊤⟩ ⊢ b : B)
    (ha : HasEff e a) (he : .del ≤ (pquant e).pos)
    : Beta Γ B _ _ (da.let₁ hΓ db) (.let₁ Γ.erase_right (.unit inferInstance) db)
  | elim_neg {Γ Γr : Ctx? α} {B : Ty α} {a b : Term φ (Ty α)}
    (hΓ : Γ.SSplit Γ Γr) (da : Γr ⊢ a : Ty.unit) (db : Γ.cons ⟨Ty.unit, ⊤⟩ ⊢ b : B)
    (ha : HasEff e a) (he : .del ≤ (pquant e).neg)
    : Beta Γ B _ _ (.let₁ Γ.erase_right (.unit inferInstance) db) (da.let₁ hΓ db)
  | beta_pos {Γ Γl Γr : Ctx? α} {A : Ty α} {a b : Term φ (Ty α)}
    (hΓ : Γ.SSplit Γl Γr) (da : Γr ⊢ a : A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
    (db : Γl.cons ⟨A, q⟩ ⊢ b : B)
    {el er} (ha : HasEff el a) (hb : HasEff er b) (he : el ⇀ er)
    (heq : q ⊓ quant A ≤ (pquant el).pos)
    : Beta Γ B _ _
      (da.let₁ hΓ (db.pwk ((Ctx?.PWk.refl Γl).cons (by simp))))
      (db.subst (SubstDS.subst0 hΓ da q hq))
  | beta_neg {Γ Γl Γr : Ctx? α} {A : Ty α} {a b : Term φ (Ty α)}
    (hΓ : Γ.SSplit Γl Γr) (da : Γr ⊢ a : A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
    (db : Γl.cons ⟨A, q⟩ ⊢ b : B)
    {el er} (ha : HasEff el a) (hb : HasEff er b) (he : el ↽ er)
    (heq : q ⊓ quant A ≤ (pquant el).neg)
    : Beta Γ B _ _
      (db.subst (SubstDS.subst0 hΓ da q hq))
      (da.let₁ hΓ (db.pwk ((Ctx?.PWk.refl Γl).cons (by simp))))
