import Refinery.Term.Extrinsic.Refinement.Uniform

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

-- class RWS.RenCongr (R : RWS φ α) where
--   ren_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A) :
--     R Γ A a b → R Γ A (a.ren ρ) (b.ren ρ)

class DRWS.DWkCongr (R : DRWS φ α) where
  dwkD_congr {Γ Δ :  Ctx? α} (ρ : Γ.Wk Δ) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A) :
    R.rel da db → R.rel (da.wkD ρ) (db.wkD ρ)

theorem DRWS.rel.wkD_of_wk {R : DRWS φ α}
  {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  (h : R.rel (da.wk ρ) (db.wk ρ)) : R.rel (da.wkD ρ) (db.wkD ρ)
  := h.of_cast_term

theorem DRWS.rel.wk_of_wkD {R : DRWS φ α}
  {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  (h : R.rel (da.wkD ρ) (db.wkD ρ)) : R.rel (da.wk ρ) (db.wk ρ)
  := h.cast_term _ _

theorem DRWS.rel.wk_iff_wkD {R : DRWS φ α}
  {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A)
  : R.rel (da.wk ρ) (db.wk ρ) ↔ R.rel (da.wkD ρ) (db.wkD ρ)
  := ⟨λh => h.wkD_of_wk, λh => h.wk_of_wkD⟩

theorem DRWS.DWkCongr.mk' {R : DRWS φ α}
  (dwk_congr :
    ∀{Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A),
      R.rel da db → R.rel (da.wk ρ) (db.wk ρ))
  : DWkCongr R where
  dwkD_congr ρ _ _ _ da db h := (dwk_congr ρ da db h).wkD_of_wk


theorem DRWS.rel.dwkD_congr [DWkCongr R]
  {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A} (h : R.rel da db)
  : R.rel (da.wkD ρ) (db.wkD ρ) := DWkCongr.dwkD_congr ρ da db h

theorem DRWS.rel.dwk_congr [DWkCongr R]
  {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A} (h : R.rel da db)
  : R.rel (da.wk ρ) (db.wk ρ) := (h.dwkD_congr ρ).cast_term _ _

instance DRWS.instDWkCongrBot : DWkCongr (⊥ : DRWS φ α) where
  dwkD_congr _ _ _ _ _ _ h := h.elim

instance DRWS.dwk_congr_symm (R : DRWS φ α) [DWkCongr R] : R.symm.DWkCongr where
  dwkD_congr ρ _ _ _ _ _ | .fwd h => .fwd (h.dwkD_congr ρ) | .bwd h => .bwd (h.dwkD_congr ρ)

class DRWS.WkCongr (R : DRWS φ α) where
  uwk_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} (da : Δ ⊢ a : A) (db : Δ ⊢ b : A) :
    R.rel da db → R.uniform.rel (da.wk ρ) (db.wk ρ)

instance DRWS.WkCongr.of_dwk_congr {R : DRWS φ α} [DWkCongr R] : WkCongr R where
  uwk_congr ρ _ _ _ _ _ h := uniform.base (h.dwk_congr ρ)

theorem DRWS.rel.uwk_congr [WkCongr R]
  {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A a b} {da : Δ ⊢ a : A} {db : Δ ⊢ b : A}
  : R.rel da db → R.uniform.rel (da.wk ρ) (db.wk ρ)
  := WkCongr.uwk_congr ρ da db

instance DRWS.dwk_congr_uniform (R : DRWS φ α) [WkCongr R] : R.uniform.DWkCongr where
  dwkD_congr {Γ Δ} ρ _ _ _ da db h := by induction h generalizing Γ with
    | pos_unif hΔ hΔc hc hd ha hs hb hei hec hsb I =>
      --TODO: simplfy
      rw [<-DRWS.rel.wk_iff_wkD]
      rename_i s Δ Δc Δl Δm Δr e e' A B X a b b' da ds db db'
      have _ : Δl.del := hΔc.left_del;
      let Γc := (hΔ.wkLeft ρ)
      let Γr := (hΔ.wkRight ρ)
      let hΓ : Γ.SSplit Γc Γr := (hΔ.wk ρ)
      let ρc : Γc.Wk Δc := (hΔ.leftWk ρ)
      let ρr : Γr.Wk Δr := (hΔ.rightWk ρ)
      have hcc : Γc.copy := (hΔ.wkLeft_copy ρ)
      have hdd : Γc.del := (hΔ.wkLeft_del ρ)
      let Γl := (hΔc.wkLeft ρc)
      let Γm := (hΔc.wkRight ρc)
      have hΓc : Γc.SSplit Γl Γm := (hΔc.wk ρc)
      have hllc : Δl.copy := hΔc.left_copy
      have hlcc : Γl.copy := hΔc.wkLeft_copy ρc
      have hldd : Γl.del := hΔc.wkLeft_del ρc
      let ρcl : Γc.PWk Γm := hΓc.pwk_left_del
      let ρl : Γl.Wk Δl := (hΔc.leftWk ρc)
      let ρm : Γm.Wk Δm := (hΔc.rightWk ρc)
      let dl := (ds.let₁ (hΔc.cons (.right _)) (db.wk1 _));
      let dr :=
          (db'.case (Δc.both.cons (.right _))
            Deriv.bv0.inl ((ds.pwk ((hΔc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
      simp only [Deriv.wk_let₁, Deriv.wk_iter] at *
      let daw := da.wk ρr
      let dsw := ds.wk (ρm.scons ⟨A, ⊤⟩)
      let dbw := (db.wk (ρl.scons ⟨X, ⊤⟩))
      let dlw := dsw.let₁ (hΓc.cons (.right _)) (dbw.wk1 ⟨A, 0⟩)
      let dbw' := db'.wk (ρc.scons ⟨A, ⊤⟩)
      let drw := dbw'.case (Γc.both.cons (.right _))
        Deriv.bv0.inl
        ((dsw.pwk (ρcl.scons _)).wk1 ⟨A, 0⟩).inr
      have ρci : ρc.ix = ρ.ix := hΔ.ix_leftWk ρ
      have ρri : ρr.ix = ρ.ix := hΔ.ix_rightWk ρ
      have ρli : ρl.ix = ρ.ix := (hΔc.ix_leftWk ρc).trans ρci
      have ρmi : ρm.ix = ρ.ix := (hΔc.ix_rightWk ρc).trans ρci
      have hdlw : (ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρm).ix s).let₁ X
        (↑¹ (b.ren (ρl.scons ⟨X , ⊤⟩))) = (s.let₁ X (↑¹ b)).ren (ρc.scons ⟨A, ⊤⟩)
        := by
        simp only [Ctx?.Wk.ix, ren, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ, ρci, ρli, ρmi]
      have hdrw :
        (b'.ren (ρc.scons ⟨A, ⊤⟩)).case B A
          (inl B X (bv 0))
          (inr B X (↑¹ (s.ren (ρm.scons ⟨A, ⊤⟩))))
        = ren (ρc.scons ⟨A, ⊤⟩) (b'.case B A (inl B X (bv 0)) (inr B X (↑¹ s)))
        := by
        simp only [Ctx?.Wk.ix, ren, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ, ρci, ρli, ρmi]
        simp only [Nat.liftWk]
      have h : R.uniform.rel dlw drw := by
        convert
          Coherent.elim _ (dlw.cast_term hdlw) _ (drw.cast_term hdrw)
            (I (ρc.scons ⟨A, ⊤⟩)).wk_of_wkD using 1
        <;> simp [Deriv.cast_term, Deriv.cast]
      let dliw := Deriv.let₁ hΓ daw
                  (Deriv.iter (hΓc.cons (.right ⟨A, ⊤⟩))
                    inferInstance inferInstance
                    dsw (dbw.wk1 ⟨A, 0⟩))
      let driw := Deriv.iter hΓ inferInstance inferInstance daw dbw'
      have h : R.uniform.rel dliw driw := DRWS.uniform.pos_unif
        (ds := dsw) (da := daw) (db := dbw) (db' := dbw') hΓ hΓc
        inferInstance inferInstance inferInstance inferInstance inferInstance hei hec h
      have hliw : (ren ρr.ix a).let₁ A
                    ((ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρm).ix s).iter X B
                      (ren (↑ⁿ Nat.succ) (ren (Ctx?.Wk.scons { ty := X, q := ⊤ } ρl).ix b))) =
                  (ren ρ.ix (a.let₁ A (s.iter X B (ren (↑ⁿ Nat.succ) b)))) := by
                  simp only [
                    Ctx?.Wk.ix, ren, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ,
                    ρci, ρli, ρmi, ρri
                  ]
      have hriw : (ren ρr.ix a).iter A B (ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρc).ix b')
                  = (ren ρ.ix (a.iter A B b')) := by simp [ρri, ρci]
      exact Coherent.elim
        (dliw.cast_term hliw) _ (driw.cast_term hriw) _
        (h.cast_term hliw hriw)
    | neg_unif hΔ hΔc hc hd ha hs hb hei hec hsb I =>
      --TODO: simplfy
      rw [<-DRWS.rel.wk_iff_wkD]
      rename_i s Δ Δc Δl Δm Δr e e' A B X a b b' da ds db db'
      have _ : Δl.del := hΔc.left_del;
      let Γc := (hΔ.wkLeft ρ)
      let Γr := (hΔ.wkRight ρ)
      let hΓ : Γ.SSplit Γc Γr := (hΔ.wk ρ)
      let ρc : Γc.Wk Δc := (hΔ.leftWk ρ)
      let ρr : Γr.Wk Δr := (hΔ.rightWk ρ)
      have hcc : Γc.copy := (hΔ.wkLeft_copy ρ)
      have hdd : Γc.del := (hΔ.wkLeft_del ρ)
      let Γl := (hΔc.wkLeft ρc)
      let Γm := (hΔc.wkRight ρc)
      have hΓc : Γc.SSplit Γl Γm := (hΔc.wk ρc)
      have hllc : Δl.copy := hΔc.left_copy
      have hlcc : Γl.copy := hΔc.wkLeft_copy ρc
      have hldd : Γl.del := hΔc.wkLeft_del ρc
      let ρcl : Γc.PWk Γm := hΓc.pwk_left_del
      let ρl : Γl.Wk Δl := (hΔc.leftWk ρc)
      let ρm : Γm.Wk Δm := (hΔc.rightWk ρc)
      let dl := (ds.let₁ (hΔc.cons (.right _)) (db.wk1 _));
      let dr :=
          (db'.case (Δc.both.cons (.right _))
            Deriv.bv0.inl ((ds.pwk ((hΔc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
      simp only [Deriv.wk_let₁, Deriv.wk_iter] at *
      let daw := da.wk ρr
      let dsw := ds.wk (ρm.scons ⟨A, ⊤⟩)
      let dbw := (db.wk (ρl.scons ⟨X, ⊤⟩))
      let dlw := dsw.let₁ (hΓc.cons (.right _)) (dbw.wk1 ⟨A, 0⟩)
      let dbw' := db'.wk (ρc.scons ⟨A, ⊤⟩)
      let drw := dbw'.case (Γc.both.cons (.right _))
        Deriv.bv0.inl
        ((dsw.pwk (ρcl.scons _)).wk1 ⟨A, 0⟩).inr
      have ρci : ρc.ix = ρ.ix := hΔ.ix_leftWk ρ
      have ρri : ρr.ix = ρ.ix := hΔ.ix_rightWk ρ
      have ρli : ρl.ix = ρ.ix := (hΔc.ix_leftWk ρc).trans ρci
      have ρmi : ρm.ix = ρ.ix := (hΔc.ix_rightWk ρc).trans ρci
      have hdlw : (ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρm).ix s).let₁ X
        (↑¹ (b.ren (ρl.scons ⟨X , ⊤⟩))) = (s.let₁ X (↑¹ b)).ren (ρc.scons ⟨A, ⊤⟩)
        := by
        simp only [Ctx?.Wk.ix, ren, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ, ρci, ρli, ρmi]
      have hdrw :
        (b'.ren (ρc.scons ⟨A, ⊤⟩)).case B A
          (inl B X (bv 0))
          (inr B X (↑¹ (s.ren (ρm.scons ⟨A, ⊤⟩))))
        = ren (ρc.scons ⟨A, ⊤⟩) (b'.case B A (inl B X (bv 0)) (inr B X (↑¹ s)))
        := by
        simp only [Ctx?.Wk.ix, ren, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ, ρci, ρli, ρmi]
        simp only [Nat.liftWk]
      have h : R.uniform.rel drw dlw := by
        convert
          Coherent.elim _ (drw.cast_term hdrw) _ (dlw.cast_term hdlw)
            (I (ρc.scons ⟨A, ⊤⟩)).wk_of_wkD using 1
        <;> simp [Deriv.cast_term, Deriv.cast]
      let dliw := Deriv.let₁ hΓ daw
                  (Deriv.iter (hΓc.cons (.right ⟨A, ⊤⟩))
                    inferInstance inferInstance
                    dsw (dbw.wk1 ⟨A, 0⟩))
      let driw := Deriv.iter hΓ inferInstance inferInstance daw dbw'
      have h : R.uniform.rel driw dliw := DRWS.uniform.neg_unif
        (ds := dsw) (da := daw) (db := dbw) (db' := dbw') hΓ hΓc
        inferInstance inferInstance inferInstance inferInstance inferInstance hei hec h
      have hliw : (ren ρr.ix a).let₁ A
                    ((ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρm).ix s).iter X B
                      (ren (↑ⁿ Nat.succ) (ren (Ctx?.Wk.scons { ty := X, q := ⊤ } ρl).ix b))) =
                  (ren ρ.ix (a.let₁ A (s.iter X B (ren (↑ⁿ Nat.succ) b)))) := by
                  simp only [
                    Ctx?.Wk.ix, ren, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ,
                    ρci, ρli, ρmi, ρri
                  ]
      have hriw : (ren ρr.ix a).iter A B (ren (Ctx?.Wk.scons { ty := A, q := ⊤ } ρc).ix b')
                  = (ren ρ.ix (a.iter A B b')) := by simp [ρri, ρci]
      exact Coherent.elim
        (driw.cast_term hriw) _ (dliw.cast_term hliw) _
        (h.cast_term hriw hliw)
    | base => apply rel.of_cast_term; apply WkCongr.uwk_congr; assumption
    | refl => apply DRWS.rel.wkD_of_wk; apply uniform.refl
    | trans => apply uniform.trans <;> apply_assumption
    | _ => simp only [Deriv.wkD]; constructor <;> apply_assumption
