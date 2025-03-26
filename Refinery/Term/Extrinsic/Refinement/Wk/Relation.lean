import Refinery.Term.Extrinsic.Refinement.Wk.Basic
import Refinery.Term.Extrinsic.Refinement.Relation

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

instance DRWS.instWkCongrLetMove : WkCongr (LetMove (S := S)) where
  uwk_congr {Γ Δ} ρ _ _ _ da db h := by cases h with
    | let_op hΓ hf da db =>
      apply DRWS.cast_eq
        (.base (.let_op (hΓ.wk ρ) hf (da.wk (hΓ.rightWk ρ)) (db.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | let_let₁ hΓ hΓc da db dc =>
      apply DRWS.cast_eq
        (.base (.let_let₁ (hΓ.wk ρ) (hΓc.wk (hΓ.rightWk ρ)) (da.wk (hΓc.rightWk (hΓ.rightWk ρ)))
        (db.wk ((hΓc.leftWk (hΓ.rightWk ρ)).scons _))
        (dc.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | let_let₂ hΓ hΓc da db dc =>
      apply DRWS.cast_eq
        (.base (.let_let₂ (hΓ.wk ρ) (hΓc.wk (hΓ.rightWk ρ)) (da.wk (hΓc.rightWk (hΓ.rightWk ρ)))
        (db.wk (((hΓc.leftWk (hΓ.rightWk ρ)).scons _).scons _))
        (dc.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
      rfl
    | let_case hΓ hΓc da db dc dd =>
      apply DRWS.cast_eq
        (.base (.let_case (hΓ.wk ρ) (hΓc.wk (hΓ.rightWk ρ)) (da.wk (hΓc.rightWk (hΓ.rightWk ρ)))
        (db.wk ((hΓc.leftWk (hΓ.rightWk ρ)).scons _))
        (dc.wk ((hΓc.leftWk (hΓ.rightWk ρ)).scons _))
        (dd.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | let_abort hΓ da db =>
      apply DRWS.cast_eq
        (.base (.let_abort (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ)) (db.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | let_iter hΓ hΓc hcm hdm hcl hdl da db dc =>
      apply DRWS.cast_eq
        (.base (.let_iter (hΓ.wk ρ) (hΓc.wk (hΓ.rightWk ρ))
        (hΓc.wkLeft_copy (hΓ.rightWk ρ))
        (hΓc.wkLeft_del (hΓ.rightWk ρ))
        (hΓ.wkLeft_copy ρ)
        (hΓ.wkLeft_del ρ)
        (da.wk ((hΓc.rightWk (hΓ.rightWk ρ))))
        (db.wk (((hΓc.leftWk (hΓ.rightWk ρ)).scons _)))
        (dc.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

instance DRWS.instWkCongrLetBind : WkCongr (LetBind (S := S)) where
  uwk_congr {Γ Δ} ρ _ _ _ da db h := by cases h with
    | bind_op hf da => apply DRWS.cast_eq (.base (.bind_op hf (da.wk ρ))) rfl rfl
    | bind_let₂ hΓ da db =>
      apply DRWS.cast_eq
        (.base (.bind_let₂ (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ))
        (db.wk (((hΓ.leftWk ρ).scons _).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | bind_case hΓ da db dc =>
      apply DRWS.cast_eq
        (.base (.bind_case (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ))
        (db.wk (((hΓ.leftWk ρ).scons _)))
        (dc.wk (((hΓ.leftWk ρ).scons _)))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | bind_iter hΓ hc hd da db =>
      apply DRWS.cast_eq
        (.base (.bind_iter (hΓ.wk ρ)
        (hΓ.wkLeft_copy ρ)
        (hΓ.wkLeft_del ρ)
        (da.wk (hΓ.rightWk ρ))
        (db.wk (((hΓ.leftWk ρ).scons _)))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

instance DRWS.instWkCongrStep : WkCongr (Step (S := S)) where
  uwk_congr {Γ Δ} ρ _ _ _ da db h := by cases h with
    | terminal db => apply DRWS.cast_eq (.base (.terminal (db.wk ρ))) rfl rfl
    | initial  hΓ da db dc =>
      apply DRWS.cast_eq
        (.base (.initial (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ))
        (db.wk ((hΓ.leftWk ρ).scons _))
        (dc.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | let₂_eta db =>
      apply DRWS.cast_eq (.base (.let₂_eta (db.wk ρ))) rfl rfl
    | case_eta db =>
      apply DRWS.cast_eq (.base (.case_eta (db.wk ρ))) rfl rfl
    | let₂_beta hΓ hΓc da db dc =>
      apply DRWS.cast_eq
        (.base (.let₂_beta (hΓ.wk ρ) (hΓc.wk (hΓ.rightWk ρ))
        (da.wk ((hΓc.leftWk (hΓ.rightWk ρ))))
        (db.wk ((hΓc.rightWk (hΓ.rightWk ρ))))
        (dc.wk (((hΓ.leftWk ρ).scons _).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | case_inl hΓ da db dc =>
      apply DRWS.cast_eq
        (.base (.case_inl (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ))
        (db.wk ((hΓ.leftWk ρ).scons _))
        (dc.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | case_inr hΓ da db dc =>
      apply DRWS.cast_eq
        (.base (.case_inr (hΓ.wk ρ) (da.wk (hΓ.rightWk ρ))
        (db.wk ((hΓ.leftWk ρ).scons _))
        (dc.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
    | fixpoint hΓ hc hd da db =>
      apply DRWS.cast_eq
        (.base (.fixpoint (hΓ.wk ρ) (hΓ.wkLeft_copy ρ) (hΓ.wkLeft_del ρ)
        (da.wk (hΓ.rightWk ρ))
        (db.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
      rfl
    | codiag hΓ hc hd da db =>
      apply DRWS.cast_eq
        (.base (.codiag (hΓ.wk ρ) (hΓ.wkLeft_copy ρ) (hΓ.wkLeft_del ρ)
        (da.wk (hΓ.rightWk ρ))
        (db.wk ((hΓ.leftWk ρ).scons _))))
      simp
      simp [ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
