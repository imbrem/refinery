import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Subst.Basic

namespace Refinery

namespace Term

--NOTE: since only pure substitutions are uniform, I believe pure substitutions can be proven
-- congruent for any UWkCongr relation, so we should be fine here in terms of expressive power
-- We should still do relD? quotienting? Maybe?

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive DRWS.relD? (R : DRWS φ α)
  : ∀{Γ} {a a' : Term φ (Ty α)} {v}, (Γ ⊢? a : v) → (Γ ⊢? a' : v) → Prop
  | valid {Γ : Ctx? α} {a a'} (A q) {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A} (h : R.rel da da') (hq)
    : relD? R (.valid A q da hq) (.valid A q da' hq)
  | zero {Γ : Ctx? α} (a a') (A) (hΓ : Γ.del) : relD? R (.zero hΓ a A) (.zero hΓ a' A)

inductive DRWS.relS (R : DRWS φ α) : ∀{Γ Δ : Ctx? α}, SubstDS φ Γ Δ → SubstDS φ Γ Δ → Prop
  | nil {Γ : Ctx? α} (hΓ : Γ.del) : relS R (.nil hΓ) (.nil hΓ)
  | cons {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr)
    {σ σ' : SubstDS φ Γl Δ} (hσ : R.relS σ σ')
    {a a'} {da : Γr ⊢? a : v} {da' : Γr ⊢? a' : v}
    (ha : R.relD? da da') : relS R (σ.cons hΓ da) (σ'.cons hΓ da')
  -- TODO: do we add transitivity here, or will it make things more complex?
  -- (note: transitivity allows for multi-splitting)

theorem DRWS.rel.substD_of_subst {R : DRWS φ α}
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  (h : R.rel (da.subst σ) (db.subst σ)) : R.rel (da.substD σ) (db.substD σ)
  := h.of_cast_term

theorem DRWS.rel.subst_of_substD {R : DRWS φ α}
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  (h : R.rel (da.substD σ) (db.substD σ)) : R.rel (da.subst σ) (db.subst σ)
  := h.cast_term _ _

theorem DRWS.rel.substD_iff_subst {R : DRWS φ α}
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  : R.rel (da.subst σ) (db.subst σ) ↔ R.rel (da.substD σ) (db.substD σ)
  := ⟨DRWS.rel.substD_of_subst _, DRWS.rel.subst_of_substD _⟩

class DRWS.SubstCongr (R : DRWS φ α) where
  csubst_congr {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A) :
    R.rel da db → R.cohere.rel (da.subst σ) (db.subst σ)

instance DRWS.SubstCongr.instBot : SubstCongr (⊥ : DRWS φ α) where
  csubst_congr _ _ _ _ _ _  h:= h.elim

theorem DRWS.rel.csubst_congr [SubstCongr R]
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  : R.rel da db → R.cohere.rel (da.subst σ) (db.subst σ)
  := SubstCongr.csubst_congr σ da db

instance DRWS.subst_congr_symm (R : DRWS φ α) [SubstCongr R] : R.symm.SubstCongr where
  csubst_congr ρ _ _ _ _ _
    | .fwd h => (h.csubst_congr ρ).mono R.symm_increasing
    | .bwd h => (h.csubst_congr ρ).toSwap.toCohere.mono R.swap_le_symm

class DRWS.USubstCongr (R : DRWS φ α) where
  usubst_congr {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A) :
    R.rel da db → R.uniform.rel (da.subst σ) (db.subst σ)

instance DRWS.USubstCongr.of_subst_congr {R : DRWS φ α} [SubstCongr R] : USubstCongr R where
  usubst_congr ρ _ _ _ _ _ h := R.uniform_le_cohere _ _ _ _ _ _ (h.csubst_congr ρ)

theorem DRWS.rel.usubst_congr [USubstCongr R]
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  : R.rel da db → R.uniform.rel (da.subst σ) (db.subst σ)
  := USubstCongr.usubst_congr σ da db

-- -- OOPS: only _pure_ substitutions are uniform!!!
-- theorem DRWS.rel.substD_congr_uniform [USubstCongr R]
--   {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
--   (h : R.uniform.rel da db) : R.uniform.rel (da.substD σ) (db.substD σ)
--   := by induction h generalizing Γ with
--   | pos_unif hΔ hΔc hc hd ha hs hb hei hec hsb I =>
--       apply substD_of_subst
--       rename_i s Δ Δc Δl Δm Δr e e' A B X a b b' da ds db db'
--       have _ : Δl.del := hΔc.left_del;
--       let Γc := (σ.inLeft hΔ)
--       let Γr := (σ.inRight hΔ)
--       let hΓ : Γ.SSplit Γc Γr := (σ.ssplitIn hΔ)
--       let σc : SubstDS φ Γc Δc := (σ.substLeft hΔ)
--       let σr : SubstDS φ Γr Δr := (σ.substRight hΔ)
--       have hcc : Γc.copy := sorry
--       have hdd : Γc.del := sorry
--       let Γl := (σc.inLeft hΔc)
--       let Γm := (σc.inRight hΔc)
--       have hΓc : Γc.SSplit Γl Γm := (σc.ssplitIn hΔc)
--       have hllc : Δl.copy := hΔc.left_copy
--       have hlcc : Γl.copy := sorry
--       have hldd : Γl.del := sorry
--       let ρcl : Γc.PWk Γm := hΓc.pwk_left_del
--       let σl : SubstDS φ Γl Δl := (σc.substLeft hΔc)
--       let σm : SubstDS φ Γm Δm := (σc.substRight hΔc)
--       let dl := (ds.let₁ (hΔc.cons (.right _)) (db.wk1 _));
--       let dr :=
--           (db'.case (Δc.both.cons (.right _))
--             Deriv.bv0.inl ((ds.pwk ((hΔc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
--       simp only [Deriv.wk_let₁, Deriv.wk_iter] at *
--       let daw := da.subst σr
--       let dsw := ds.subst (σm.lift ⟨A, ⊤⟩)
--       let dbw := (db.subst (σl.lift ⟨X, ⊤⟩))
--       let dlw := dsw.let₁ (hΓc.cons (.right _)) (dbw.wk1 ⟨A, 0⟩)
--       let dbw' := db'.subst (σc.lift ⟨A, ⊤⟩)
--       let drw := dbw'.case (Γc.both.cons (.right _))
--         Deriv.bv0.inl
--         ((dsw.pwk (ρcl.scons _)).wk1 ⟨A, 0⟩).inr
--       have hdlw : (s.subst (σm.lift ⟨A, ⊤⟩)).let₁ X
--         (↑¹ (b.subst (σl.lift ⟨X , ⊤⟩))) = (s.let₁ X (↑¹ b)).subst (σc.lift ⟨A, ⊤⟩)
--         := by sorry
--       have hdrw :
--         (b'.subst (σc.lift ⟨A, ⊤⟩)).case B A
--           (inl B X (bv 0))
--           (inr B X (↑¹ (s.subst (σm.lift ⟨A, ⊤⟩))))
--         = subst (σc.lift ⟨A, ⊤⟩) (b'.case B A (inl B X (bv 0)) (inr B X (↑¹ s)))
--         := by sorry
--       have h : R.uniform.rel dlw drw := by
--         convert
--           Coherent.elim _ (dlw.cast_term hdlw) _ (drw.cast_term hdrw)
--             (I (σc.lift ⟨A, ⊤⟩)).subst_of_substD using 1
--         <;> simp [Deriv.cast_term, Deriv.cast]
--       let dliw := Deriv.let₁ hΓ daw
--                   (Deriv.iter (hΓc.cons (.right ⟨A, ⊤⟩))
--                     inferInstance inferInstance
--                     dsw (dbw.wk1 ⟨A, 0⟩))
--       let driw := Deriv.iter hΓ inferInstance inferInstance daw dbw'
--       have h : R.uniform.rel dliw driw := DRWS.uniform.pos_unif
--         (ds := dsw) (da := daw) (db := dbw) (db' := dbw') hΓ hΓc
--         inferInstance inferInstance inferInstance inferInstance inferInstance hei hec h
--       have hliw : (ren ρr.ix a).let₁ A
--                     ((ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρm).ix s).iter X B
--                       (ren (↑ⁿ Nat.succ) (ren (Ctx?.Wk.scons { ty := X, q := ⊤ } ρl).ix b))) =
--                   (ren ρ.ix (a.let₁ A (s.iter X B (ren (↑ⁿ Nat.succ) b)))) := by
--                   simp only [
--                     Ctx?.Wk.ix, ren, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ,
--                     ρci, ρli, ρmi, ρri
--                   ]
--       have hriw : (ren ρr.ix a).iter A B (ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρc).ix b')
--                   = (ren ρ.ix (a.iter A B b')) := by simp [ρri, ρci]
--       exact Coherent.elim
--         (dliw.cast_term hliw) _ (driw.cast_term hriw) _
--         (h.cast_term hliw hriw)
--   | neg_unif hΔ hΔc hc hd ha hs hb hei hec hsb I => sorry
--   | base => apply rel.of_cast_term; apply USubstCongr.usubst_congr; assumption
--   | refl =>  apply rel.substD_of_subst; apply uniform.refl
--   | trans => apply uniform.trans <;> apply_assumption
--   | _ => stop simp only [Deriv.substD]; constructor <;> apply_assumption
