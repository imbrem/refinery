import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Semantics.Minimal
import Refinery.Term.Extrinsic.Semantics.Effect

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open ChosenFiniteCoproducts

open scoped MonoidalCategory

open HasCommRel

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

class RWS.Valid (R : RWS φ α) (C : Type _)
  [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
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
    have hΓl_copy := hΓc.left_copy
    have hΓl_del := hΓc.left_del
    have hΓm_copy := hΓc.right_copy
    have hΓm_del := hΓc.right_del
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
    rw [<-Category.assoc (f := css⟦_⟧)]
    apply (Elgot2.right_mover_right_uniform he).right_uniform
    apply EffectfulCategory.HasEff.has_eff
    apply EffectfulCategory.HasEff.has_eff
    apply EffectfulCategory.HasEff.has_eff
    let hIa_left : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B.coprod X⟧ :=
      hΓc.den (C := C) ▷ _ ≫
        (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ t⟦A⟧).hom ≫ t⟦Γl.ety⟧ ◁ Dms.den ≫ Dlb.den;
    let hIa_right : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B.coprod X⟧ :=
      Δ_ Γc.ety ▷ (t⟦A⟧ : C) ≫
        (α_ t⟦Γc.ety⟧ t⟦Γc.ety⟧ t⟦A⟧).hom ≫
        t⟦Γc.ety⟧ ◁ Dcb'.den ≫
        (∂L t⟦Γc.ety⟧ t⟦B⟧ t⟦A⟧).inv ≫
        (
          (!_ (Γc.ety) ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom) ⊕ₕ
          ((Deriv.pwk (Ctx?.PWk.scons { ty := A, q := ⊤ } hΓc.pwk_left_del) Dms).den))
    let iter_left : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B⟧ ⊕ₒ (t⟦Γl.ety⟧ ⊗ 𝟙_ C) ⊗ t⟦X⟧ :=
      Δ_ Γc.ety ▷ t⟦A⟧ ≫
      pw⟦hΓc.pwk_right_del⟧ ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
      _ ◁ hIa_left ≫
      (∂L _ _ _).inv ≫
      ((!_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom) ⊕ₕ ((ρ_ _).inv ▷ _))
    let iter_right : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B⟧ ⊕ₒ (t⟦Γl.ety⟧ ⊗ 𝟙_ C) ⊗ t⟦X⟧ :=
      Δ_ Γc.ety ▷ t⟦A⟧ ≫
        pw⟦hΓc.pwk_right_del⟧ ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
        _◁ hIa_right ≫
        (∂L _ _ _).inv ≫
        ((!_ _ ▷ _ ≫ (λ_ _).hom) ⊕ₕ ((ρ_ _).inv ▷ _))
    convert_to iter_left ↠ iter_right
    · simp only [
        iter_left, Ctx?.SSplit.den, Var?.SSplit.den, tensorHom_def, Category.assoc, Var?.ety_erase,
        Ty.den, swap_inner_leftUnitor_assoc, Ctx?.ety, M.copy_tensor, M.copy_unit, Ctx?.den,
        hIa_left, Deriv.den_wk1, swap_inner_tensorUnit_right,
      ]
      -- rw [
      --   <-Central.left_exchange_assoc, <-comp_whiskerRight_assoc,
      --   <-rightUnitor_inv_naturality_assoc, swap_inner_tensorUnit_right,
      --   Deriv.den_wk1,
      -- ]
      -- simp only [
      --   Var?.ety_erase, M.drop_unit, Var?.ety, ety_var, PremonoidalCategory.comp_whiskerRight,
      --   Category.assoc, <-associator_naturality_left_assoc, <-associator_naturality_middle_assoc,
      --   <-associator_naturality_left_assoc,
      -- ]
      sorry
    · sorry
    stop
    simp only [iter_left, iter_right]
    apply refines_comp
    rfl
    apply refines_comp
    rfl
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerLeft
    convert hIa
    · sorry
    · sorry
    rfl
  | neg_unif hΓ hΓc hc hd hei he Dra ha Dms hs Dlb hb Dcb' hb' rs Ia =>
    stop
    rename_i s Γ Γc Γl Γm Γr e e' A B X a b b'
    have hΓl_copy := hΓc.left_copy
    have hΓl_del := hΓc.left_del
    have hΓm_copy := hΓc.right_copy
    have hΓm_del := hΓc.right_del
    let Da' := (Dra.let₁ hΓ (Dms.iter (hΓc.cons (.right _)) inferInstance inferInstance (Dlb.wk1 _)))
    let Db' := (Dra.iter hΓ inferInstance inferInstance Dcb')
    have Γm_copy := hΓc.right_copy
    have hIa := Ia
                  (Dcb'.case (Γc.both.cons (.right _))
                    (Deriv.bv (.here inferInstance Var?.Wk.top_le_quant)).inl
                    ((Dms.pwk ((hΓc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
                  (Dms.let₁ (hΓc.cons (.right _)) (Dlb.wk1 _))
    convert_to Db'.den ↠ Da'.den
    apply Deriv.coherence
    apply Deriv.coherence
    simp only [Da', Db', Deriv.den]
    apply refines_comp
    rfl
    apply refines_comp
    rfl
    rw [<-Category.assoc (f := css⟦_⟧)]
    apply (Elgot2.left_mover_left_uniform he).left_uniform
    apply EffectfulCategory.HasEff.has_eff
    apply EffectfulCategory.HasEff.has_eff
    apply EffectfulCategory.HasEff.has_eff
    let hIa_left : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B.coprod X⟧ :=
      hΓc.den (C := C) ▷ _ ≫
        (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ t⟦A⟧).hom ≫ t⟦Γl.ety⟧ ◁ Dms.den ≫ Dlb.den;
    let hIa_right : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B.coprod X⟧ :=
      Δ_ Γc.ety ▷ (t⟦A⟧ : C) ≫
        (α_ t⟦Γc.ety⟧ t⟦Γc.ety⟧ t⟦A⟧).hom ≫
        t⟦Γc.ety⟧ ◁ Dcb'.den ≫
        (∂L t⟦Γc.ety⟧ t⟦B⟧ t⟦A⟧).inv ≫
        (
          (!_ (Γc.ety) ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom) ⊕ₕ
          ((Deriv.pwk (Ctx?.PWk.scons { ty := A, q := ⊤ } hΓc.pwk_left_del) Dms).den))
    let iter_left : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B⟧ ⊕ₒ (t⟦Γl.ety⟧ ⊗ 𝟙_ C) ⊗ t⟦X⟧ :=
      Δ_ Γc.ety ▷ t⟦A⟧ ≫
      pw⟦hΓc.pwk_right_del⟧ ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
      _ ◁ hIa_left ≫
      (∂L _ _ _).inv ≫
      ((!_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom) ⊕ₕ ((ρ_ _).inv ▷ _))
    let iter_right : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B⟧ ⊕ₒ (t⟦Γl.ety⟧ ⊗ 𝟙_ C) ⊗ t⟦X⟧ :=
      Δ_ Γc.ety ▷ t⟦A⟧ ≫
        pw⟦hΓc.pwk_right_del⟧ ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
        _◁ hIa_right ≫
        (∂L _ _ _).inv ≫
        ((!_ _ ▷ _ ≫ (λ_ _).hom) ⊕ₕ ((ρ_ _).inv ▷ _))
    convert_to iter_right ↠ iter_left
    · sorry
    · sorry
    simp only [iter_left, iter_right]
    apply refines_comp
    rfl
    apply refines_comp
    rfl
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerLeft
    convert hIa
    · sorry
    · sorry
    rfl
  | _ => sorry
