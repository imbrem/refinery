import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Subst.Effect

namespace Refinery

namespace Term

--NOTE: since only pure substitutions are uniform, I believe pure substitutions can be proven
-- congruent for any UWkCongr relation, so we should be fine here in terms of expressive power
-- We should still do relD? quotienting? Maybe?

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive DRWS.relD? (R : DRWS φ α)
  : ∀{Γ} {a a' : Term φ (Ty α)} {v}, (Γ ⊢? a : v) → (Γ ⊢? a' : v) → Prop
  | valid {Γ : Ctx? α} {a a'} (A q) {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A}
    (h : R.uniform.rel da da') (hq) : relD? R (.valid A q da hq) (.valid A q da' hq)
  | zero {Γ : Ctx? α} (a a') (A) (hΓ : Γ.del) : relD? R (.zero hΓ a A) (.zero hΓ a' A)

@[simp]
theorem DRWS.relD?.refl {R : DRWS φ α} {Γ : Ctx? α} {a : Term φ (Ty α)} {v}
  (da : Γ ⊢? a : v) : R.relD? da da
  := by induction da <;> constructor; apply DRWS.uniform.refl

inductive DRWS.relS (R : DRWS φ α) : ∀{Γ Δ : Ctx? α}, SubstDS φ Γ Δ → SubstDS φ Γ Δ → Prop
  | nil {Γ : Ctx? α} (hΓ : Γ.del) : relS R (.nil hΓ) (.nil hΓ)
  | cons {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr)
    {σ σ' : SubstDS φ Γl Δ} (hσ : R.relS σ σ')
    {a a'} {da : Γr ⊢? a : v} {da' : Γr ⊢? a' : v}
    (ha : R.relD? da da') : relS R (σ.cons hΓ da) (σ'.cons hΓ da')
  -- TODO: do we add transitivity here, or will it make things more complex?
  -- (note: transitivity allows for multi-splitting)

@[simp]
theorem DRWS.relS.refl {R : DRWS φ α} {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) : R.relS σ σ
  := by induction σ <;> constructor <;> simp [*]

structure DRWS.relSSplit (R : DRWS φ α) {Γ Δ Δl Δr : Ctx? α} (σ σ' : SubstSSplit φ Γ Δ Δl Δr )
  : Prop where
  inLeft : σ.inLeft = σ'.inLeft
  inRight : σ.inRight = σ'.inRight
  ssplitIn : σ.ssplitIn = inLeft ▸ inRight ▸ σ'.ssplitIn
  substLeft : R.relS σ.substLeft (inLeft ▸ σ'.substLeft)
  substRight : R.relS σ.substRight (inRight ▸ σ'.substRight)

@[simp]
theorem DRWS.relSSplit.refl {R : DRWS φ α} {Γ Δ Δl Δr : Ctx? α}
  (σ : SubstSSplit φ Γ Δ Δl Δr) : R.relSSplit σ σ
  := ⟨rfl, rfl, rfl, by simp, by simp⟩

theorem DRWS.relSSplit.cons {R : DRWS φ α} {Γ Γl Γr Γl' Γr' Δ Δl Δr : Ctx? α}
  {a a' : Term φ (Ty α)}
  (hΓ : Γ.SSplit Γl Γr) (hΓ' : Γ.SSplit Γl' Γr')
  (hΓl : Γl.SSplit Γll Γlr) (hΓr : Γr.SSplit Γrl Γrr)
  (hΓl' : Γl'.SSplit Γll' Γlr') (hΓr' : Γr'.SSplit Γrl' Γrr')
  (σl : SubstDS φ Γll Δl) (σr : SubstDS φ Γrl Δr)
  (dal : Γlr ⊢? a : vl) (dar : Γrr ⊢? a : vr)
  (σl' : SubstDS φ Γll' Δl) (σr' : SubstDS φ Γrl' Δr)
  (dal' : Γlr' ⊢? a' : vl) (dar' : Γrr' ⊢? a' : vr)
  (Γle : Γl = Γl') (Γre : Γr = Γr')
  (hΓe : hΓ = Γle ▸ Γre ▸ hΓ')
  : R.relSSplit (Δ := (Δ.cons v)) (Δl := (Δl.cons vl)) (Δr := (Δr.cons vr))
    ⟨Γl, Γr, hΓ, σl.cons hΓl dal, σr.cons hΓr dar⟩
    ⟨Γl', Γr', hΓ', σl'.cons hΓl' dal', σr'.cons hΓr' dar'⟩
  := sorry

theorem DRWS.relS.split {R : DRWS φ α} {Γ Δ Δl Δr : Ctx? α}
  {σ σ' : SubstDS φ Γ Δ} (hσ : R.relS σ σ') (hΔ : Δ.SSplit Δl Δr) :
  R.relSSplit (σ.ssplit hΔ) (σ'.ssplit hΔ)
  := by induction hΔ generalizing Γ with
  | nil => cases hσ; simp [SubstDS.ssplit]
  | cons hΔ hvw IΔ => cases hσ with
  | cons hΓ hσ ha =>
    rename_i σ σ'
    cases ha with
    | valid =>
      cases hvw with
      | left =>
        apply DRWS.relSSplit.cons <;> sorry
      | right =>
        apply DRWS.relSSplit.cons <;> sorry
      | sboth =>
        apply DRWS.relSSplit.cons <;> sorry
    | zero =>
      cases hvw with
      | left =>
        apply DRWS.relSSplit.cons <;> sorry
      | right =>
        apply DRWS.relSSplit.cons <;> sorry
      | sboth =>
        apply DRWS.relSSplit.cons <;> sorry

-- theorem RWS.subst_congr_uniform {R : DRWS φ α}
--   {Γ Δ : Ctx? α} (σ σ' : SubstDS φ Γ Δ) (hσ : R.relS σ σ') {A a} (da : Δ ⊢ a : A)
--   : R.toRWS.uniform Γ A (subst σ.toSubst a) (subst σ'.toSubst a)
--   := by
--   induction da generalizing Γ with
--   | bv => sorry
--   | let₁ hΔ da db Ia Ib =>
--     rename_i Δ Δl Δr A B a b
--     let Γl := σ.inLeft hΔ
--     let Γr := σ.inRight hΔ
--     let hΓ := σ.ssplitIn hΔ
--     let σl : SubstDS φ Γl Δl := σ.substLeft hΔ
--     let σr : SubstDS φ Γr Δr := σ.substRight hΔ
--     simp only [subst]
--     sorry
--   | _ =>
--     sorry

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

class DRWS.PSubstCongr (R : DRWS φ α) where
  psubst_congr {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) (hσ : σ.HasEff ⊥) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A) :
    R.rel da db → R.uniform.rel (da.subst σ) (db.subst σ)

theorem DRWS.rel.substD_congr_uniform [PSubstCongr R]
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff ⊥] {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  (h : R.uniform.rel da db) : R.uniform.rel (da.substD σ) (db.substD σ)
  := by induction h generalizing Γ with
  | pos_unif hΔ hΔc hc hd ha hs hb hei hec hsb I =>
    apply substD_of_subst
    rename_i s Δ Δc Δl Δm Δr e e' A B X a b b' da ds db db'
    have _ : Δl.del := hΔc.left_del;
    let Γc := (σ.inLeft hΔ)
    let Γr := (σ.inRight hΔ)
    let hΓ : Γ.SSplit Γc Γr := (σ.ssplitIn hΔ)
    let σc : SubstDS φ Γc Δc := (σ.substLeft hΔ)
    let σr : SubstDS φ Γr Δr := (σ.substRight hΔ)
    have hcc : Γc.copy := σ.split_copy_left hΔ
    have hdd : Γc.del := σ.split_del_left hΔ
    let Γl := (σc.inLeft hΔc)
    let Γm := (σc.inRight hΔc)
    have hΓc : Γc.SSplit Γl Γm := (σc.ssplitIn hΔc)
    have hllc : Δl.copy := hΔc.left_copy
    have hlcc : Γl.copy := σc.split_copy_left hΔc
    have hldd : Γl.del := σc.split_del_left hΔc
    let ρcl : Γc.PWk Γm := hΓc.pwk_left_del
    let σl : SubstDS φ Γl Δl := (σc.substLeft hΔc)
    let σm : SubstDS φ Γm Δm := (σc.substRight hΔc)
    let dl := (ds.let₁ (hΔc.cons (.right _)) (db.wk1 _));
    let dr :=
        (db'.case (Δc.both.cons (.right _))
          Deriv.bv0.inl ((ds.pwk ((hΔc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
    simp only [Deriv.wk_let₁, Deriv.wk_iter] at *
    let daw := da.subst σr
    let dsw := ds.subst (σm.lift ⟨A, ⊤⟩)
    let dbw := (db.subst (σl.lift ⟨X, ⊤⟩))
    let dlw := dsw.let₁ (hΓc.cons (.right _)) (dbw.wk1 ⟨A, 0⟩)
    let dbw' := db'.subst (σc.lift ⟨A, ⊤⟩)
    let drw := dbw'.case (Γc.both.cons (.right _))
      Deriv.bv0.inl
      ((dsw.pwk (ρcl.scons _)).wk1 ⟨A, 0⟩).inr
    have hdlw : (s.subst (σm.lift ⟨A, ⊤⟩)).let₁ X
      (↑¹ (b.subst (σl.lift ⟨X , ⊤⟩))) = (s.let₁ X (↑¹ b)).subst (σc.lift ⟨A, ⊤⟩)
      := by
        simp [<-subst_renOut, <-subst_renIn, σm, σl]
        congr
        ext x; cases x
        rfl
        simp [ren_ren]
        rfl
    have hdrw :
      (b'.subst (σc.lift ⟨A, ⊤⟩)).case B A
        (inl B X (bv 0))
        (inr B X (↑¹ (s.subst (σm.lift ⟨A, ⊤⟩))))
      = subst (σc.lift ⟨A, ⊤⟩) (b'.case B A (inl B X (bv 0)) (inr B X (↑¹ s)))
      := by
        simp [<-subst_renOut, <-subst_renIn, σm]
        congr
        ext x; cases x
        rfl
        simp [ren_ren]
        rfl
    have h : R.uniform.rel dlw drw := by
      convert
        Coherent.elim _ (dlw.cast_term hdlw) _ (drw.cast_term hdrw)
          (I (σc.lift ⟨A, ⊤⟩)).subst_of_substD using 1
      <;> simp [Deriv.cast_term, Deriv.cast]
    let dliw := Deriv.let₁ hΓ daw
                (Deriv.iter (hΓc.cons (.right ⟨A, ⊤⟩))
                  inferInstance inferInstance
                  dsw (dbw.wk1 ⟨A, 0⟩))
    let driw := Deriv.iter hΓ inferInstance inferInstance daw dbw'
    have h : R.uniform.rel dliw driw := DRWS.uniform.pos_unif
      (ds := dsw) (da := daw) (db := dbw) (db' := dbw') hΓ hΓc
      inferInstance inferInstance
      (SubstDS.effect_pure _ _ da)
      (SubstDS.effect_pure _ _ ds)
      (SubstDS.effect_pure _ _ db)
      hei hec h
    have hliw : (subst σr.toSubst a).let₁ A
                  ((subst (σm.lift ⟨A, ⊤⟩).toSubst s).iter X B
                    (ren (↑ⁿ Nat.succ) (subst (σl.lift ⟨X, ⊤⟩).toSubst b))) =
                (subst σ.toSubst (a.let₁ A (s.iter X B (ren (↑ⁿ Nat.succ) b)))) := by
                simp [σr, σm, σc, σl, <-subst_renOut, <-subst_renIn]
                congr
                ext x; cases x
                rfl
                simp [ren_ren]
                rfl
    have hriw : (subst σr.toSubst a).iter A B (subst (σc.lift ⟨A, ⊤⟩).toSubst b')
                = (subst σ.toSubst (a.iter A B b'))
                := by simp [σr, σc, <-subst_renOut, <-subst_renIn]
    exact Coherent.elim
      (dliw.cast_term hliw) _ (driw.cast_term hriw) _
      (h.cast_term hliw hriw)
  | neg_unif hΔ hΔc hc hd ha hs hb hei hec hsb I =>
      apply substD_of_subst
      rename_i s Δ Δc Δl Δm Δr e e' A B X a b b' da ds db db'
      have _ : Δl.del := hΔc.left_del;
      let Γc := (σ.inLeft hΔ)
      let Γr := (σ.inRight hΔ)
      let hΓ : Γ.SSplit Γc Γr := (σ.ssplitIn hΔ)
      let σc : SubstDS φ Γc Δc := (σ.substLeft hΔ)
      let σr : SubstDS φ Γr Δr := (σ.substRight hΔ)
      have hcc : Γc.copy := σ.split_copy_left hΔ
      have hdd : Γc.del := σ.split_del_left hΔ
      let Γl := (σc.inLeft hΔc)
      let Γm := (σc.inRight hΔc)
      have hΓc : Γc.SSplit Γl Γm := (σc.ssplitIn hΔc)
      have hllc : Δl.copy := hΔc.left_copy
      have hlcc : Γl.copy := σc.split_copy_left hΔc
      have hldd : Γl.del := σc.split_del_left hΔc
      let ρcl : Γc.PWk Γm := hΓc.pwk_left_del
      let σl : SubstDS φ Γl Δl := (σc.substLeft hΔc)
      let σm : SubstDS φ Γm Δm := (σc.substRight hΔc)
      let dl := (ds.let₁ (hΔc.cons (.right _)) (db.wk1 _));
      let dr :=
          (db'.case (Δc.both.cons (.right _))
            Deriv.bv0.inl ((ds.pwk ((hΔc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
      simp only [Deriv.wk_let₁, Deriv.wk_iter] at *
      let daw := da.subst σr
      let dsw := ds.subst (σm.lift ⟨A, ⊤⟩)
      let dbw := (db.subst (σl.lift ⟨X, ⊤⟩))
      let dlw := dsw.let₁ (hΓc.cons (.right _)) (dbw.wk1 ⟨A, 0⟩)
      let dbw' := db'.subst (σc.lift ⟨A, ⊤⟩)
      let drw := dbw'.case (Γc.both.cons (.right _))
        Deriv.bv0.inl
        ((dsw.pwk (ρcl.scons _)).wk1 ⟨A, 0⟩).inr
      have hdlw : (s.subst (σm.lift ⟨A, ⊤⟩)).let₁ X
        (↑¹ (b.subst (σl.lift ⟨X , ⊤⟩))) = (s.let₁ X (↑¹ b)).subst (σc.lift ⟨A, ⊤⟩)
        := by
          simp [<-subst_renOut, <-subst_renIn, σm, σl]
          congr
          ext x; cases x
          rfl
          simp [ren_ren]
          rfl
      have hdrw :
        (b'.subst (σc.lift ⟨A, ⊤⟩)).case B A
          (inl B X (bv 0))
          (inr B X (↑¹ (s.subst (σm.lift ⟨A, ⊤⟩))))
        = subst (σc.lift ⟨A, ⊤⟩) (b'.case B A (inl B X (bv 0)) (inr B X (↑¹ s)))
        := by
          simp [<-subst_renOut, <-subst_renIn, σm]
          congr
          ext x; cases x
          rfl
          simp [ren_ren]
          rfl
      have h : R.uniform.rel drw dlw := by
        convert
          Coherent.elim _ (drw.cast_term hdrw) _ (dlw.cast_term hdlw)
            (I (σc.lift ⟨A, ⊤⟩)).subst_of_substD using 1
        <;> simp [Deriv.cast_term, Deriv.cast]
      let dliw := Deriv.let₁ hΓ daw
                  (Deriv.iter (hΓc.cons (.right ⟨A, ⊤⟩))
                    inferInstance inferInstance
                    dsw (dbw.wk1 ⟨A, 0⟩))
      let driw := Deriv.iter hΓ inferInstance inferInstance daw dbw'
      have h : R.uniform.rel driw dliw := DRWS.uniform.neg_unif
        (ds := dsw) (da := daw) (db := dbw) (db' := dbw') hΓ hΓc
        inferInstance inferInstance
        (SubstDS.effect_pure _ _ da)
        (SubstDS.effect_pure _ _ ds)
        (SubstDS.effect_pure _ _ db)
        hei hec h
      have hliw : (subst σr.toSubst a).let₁ A
                    ((subst (σm.lift ⟨A, ⊤⟩).toSubst s).iter X B
                      (ren (↑ⁿ Nat.succ) (subst (σl.lift ⟨X, ⊤⟩).toSubst b))) =
                  (subst σ.toSubst (a.let₁ A (s.iter X B (ren (↑ⁿ Nat.succ) b)))) := by
                    simp [<-subst_renOut, <-subst_renIn, σm, σl, σr, σc]
                    congr
                    ext x; cases x
                    rfl
                    simp [ren_ren]
                    rfl
      have hriw : (subst σr.toSubst a).iter A B (subst (σc.lift ⟨A, ⊤⟩).toSubst b')
                  = (subst σ.toSubst (a.iter A B b')) := by
          simp [<-subst_renOut, <-subst_renIn, σm, σr, σc]
      exact Coherent.elim
        (driw.cast_term hriw) _ (dliw.cast_term hliw) _
        (h.cast_term hriw hliw)
  | base => apply rel.of_cast_term; apply PSubstCongr.psubst_congr <;> assumption
  | refl =>  apply rel.substD_of_subst; apply uniform.refl
  | trans => apply uniform.trans <;> apply_assumption
  | _ => simp only [Deriv.substD]; constructor <;> apply_assumption
