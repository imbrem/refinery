import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Semantics.Minimal
import Refinery.Term.Extrinsic.Semantics.Effect

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open HasCommRel

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]

class RWS.Valid (R : RWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [Model φ α ε C]
  : Prop where
  den_ref {Γ A a b} (h : R Γ A a b) (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) ↠ Db.den

instance RWS.instValidBot : Valid (φ := φ) ⊥ C where den_ref h := h.elim

theorem RWS.uniform.ref {R : RWS φ α} [V : R.Valid C] {Γ A a b} (h : uniform R Γ A a b)
  (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) ↠ Db.den := by induction h with
  -- | base h => apply V.den_ref h
  -- | refl => apply refines_of_eq; apply Deriv.coherence
  -- | trans hab hbc I I' => have ⟨Db'⟩ := hbc.wt.left; exact refines_trans (I Da Db') (I' Db' Db)
  -- | let₁ hΓ ra rb Ia Ib =>
  --   have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
  --   have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
  --   convert_to (Dax.let₁ hΓ Dbx).den (C := C) ↠ (Day.let₁ hΓ Dby).den
  --   apply Deriv.coherence
  --   apply Deriv.coherence
  --   simp only [Deriv.den]
  --   apply refines_comp
  --   rfl
  --   apply refines_comp
  --   apply refines_whiskerLeft
  --   exact Ia Dax Day
  --   exact Ib Dbx Dby
  -- | let₂ hΓ ra rb Ia Ib =>
  --   have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
  --   have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
  --   convert_to (Dax.let₂ hΓ Dbx).den (C := C) ↠ (Day.let₂ hΓ Dby).den
  --   apply Deriv.coherence
  --   apply Deriv.coherence
  --   simp only [Deriv.den]
  --   apply refines_comp
  --   rfl
  --   apply refines_comp
  --   apply refines_whiskerLeft
  --   exact Ia Dax Day
  --   apply refines_comp
  --   rfl
  --   exact Ib Dbx Dby
  -- | pair hΓ ra rb Ia Ib =>
  --   have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
  --   have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
  --   convert_to (Dax.pair hΓ Dbx).den (C := C) ↠ (Day.pair hΓ Dby).den
  --   apply Deriv.coherence
  --   apply Deriv.coherence
  --   simp only [Deriv.den]
  --   apply refines_comp
  --   rfl
  --   apply refines_comp
  --   apply refines_whiskerRight
  --   exact Ia Dax Day
  --   apply refines_whiskerLeft
  --   exact Ib Dbx Dby
  -- | inl | inr | abort =>
  --   cases Da; cases Db;
  --   simp only [Deriv.den]
  --   apply refines_comp
  --   apply_assumption
  --   rfl
  -- | iter hΓ hc hd ra rb Ia Ib =>
  --   have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
  --   have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
  --   convert_to (Dax.iter hΓ hc hd Dbx).den (C := C) ↠ (Day.iter hΓ hc hd Dby).den
  --   apply Deriv.coherence
  --   apply Deriv.coherence
  --   simp only [Deriv.den]
  --   apply refines_comp
  --   rfl
  --   apply refines_comp
  --   apply refines_whiskerLeft
  --   exact Ia Dax Day
  --   apply refines_iterate
  --   apply refines_comp
  --   rfl
  --   apply refines_comp
  --   rfl
  --   apply refines_comp
  --   apply refines_whiskerLeft
  --   exact Ib Dbx Dby
  --   rfl
  | pos_unif hΓ hΓc hc hd hei he Dra ha Dms hs Dlb hb Dcb' hb' rs Ia =>
    rename_i s Γ Γc Γl Γm Γr e e' A B X a b b'
    have _ := hΓc.left_copy
    have _ := hΓc.left_del
    let Da' := (Dra.let₁ hΓ (Dms.iter (hΓc.cons (.right _)) inferInstance inferInstance (Dlb.wk1 _)))
    let Db' := (Dra.iter hΓ inferInstance inferInstance Dcb')
    have Γm_copy := hΓc.right_copy
    have hIa := Ia (Dms.let₁ (hΓc.cons (.right _)) (Dlb.wk1 _))
                  (Dcb'.case (Γc.both.cons (.right _))
                    (Deriv.bv (.here inferInstance Var?.Wk.top_le_quant)).inl
                    ((Dms.pwk ((hΓc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
    convert_to Da'.den ↠ Db'.den
    apply Deriv.coherence
    apply Deriv.coherence
    simp only [Da', Db', Deriv.den]
    apply refines_comp
    rfl
    apply refines_comp
    rfl
    rw [<-Category.assoc]
    apply (Elgot2.right_mover_right_uniform he).right_uniform
    apply EffectfulCategory.HasEff.has_eff
    apply EffectfulCategory.HasEff.has_eff
    apply EffectfulCategory.HasEff.has_eff
    stop
    simp [Deriv.den] at hIa
    simp
    sorry
  | neg_unif => sorry
  | _ => sorry
