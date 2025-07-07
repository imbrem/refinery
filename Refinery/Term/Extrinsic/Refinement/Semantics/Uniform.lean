import Refinery.Term.Extrinsic.Refinement.Semantics.Valid

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

theorem uniformLeftIndHelper {Γc Γl Γm : Ctx? α}
  (hΓc : Γc.SSplit Γl Γm) {A B X : Ty α}
  (f : (t⟦Γm.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦X⟧) (g : (t⟦Γl.ety⟧ ⊗ t⟦X⟧ : C) ⟶ t⟦B⟧ ⊕ₒ t⟦X⟧) :
  hΓc.den (C := C) ▷ _ ≫ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ t⟦A⟧).hom ≫ t⟦Γl.ety⟧ ◁ f ≫ g =
  css⟦hΓc.cons (Var?.SSplit.right { ty := A, q := ⊤ })⟧ ≫
    g⟦Γl.cons ⟨A, 0⟩⟧ ◁ f ≫
      (t⟦Γl.ety⟧ ◁ !_ Ty.unit) ▷ t⟦X⟧ ≫
        (ρ_ t⟦Γl.ety⟧).hom ▷ t⟦X⟧ ≫ g
  := by simp [Ctx?.SSplit.den, tensorHom_def]; premonoidal

theorem uniformRightIndHelper {Γc Γl Γm : Ctx? α}
  [hΓc_copy : Γc.copy] [hΓc_del : Γc.del] [hΓl_del : Γl.del]
  (hΓc : Γc.SSplit Γl Γm) {A B X : Ty α}
  (f : (t⟦Γm.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦X⟧) (g : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B⟧ ⊕ₒ t⟦A⟧) :
  Δ_ Γc.ety ▷ (t⟦A⟧ : C) ≫
        (α_ t⟦Γc.ety⟧ t⟦Γc.ety⟧ t⟦A⟧).hom ≫
        t⟦Γc.ety⟧ ◁ g ≫
        (∂L t⟦Γc.ety⟧ t⟦B⟧ t⟦A⟧).inv ≫
        (
          (!_ (Γc.ety) ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom) ⊕ₕ
          (pw⟦hΓc.pwk_left_del.scons ⟨A, ⊤⟩⟧ ≫ f)) =
  css⟦Γc.both.cons (Var?.SSplit.right { ty := A, q := ⊤ })⟧ ≫
      g⟦Γc.cons ⟨A, 0⟩⟧ ◁ g ≫
        (∂L g⟦Γc.cons ⟨A, 0⟩⟧ t⟦B⟧ t⟦A⟧).inv ≫
          desc
            (((!_ (Γc.cons ⟨A, 0⟩).ety ⊗ 𝟙 t⟦B⟧) ≫
                (λ_ t⟦B⟧).hom) ≫
              ChosenFiniteCoproducts.inl t⟦B⟧ t⟦X⟧)
            (((t⟦Γc.ety⟧ ◁ !_ Ty.unit) ▷ t⟦A⟧ ≫
                (ρ_ t⟦Γc.ety⟧).hom ▷ t⟦A⟧ ≫
                  pw⟦hΓc.pwk_left_del.scons ⟨A, ⊤⟩⟧ ≫ f) ≫
              ChosenFiniteCoproducts.inr t⟦B⟧ t⟦X⟧)
  := by
  simp only [
    Ctx?.SSplit.den, Ctx?.SSplit.den_both, tensorHom_def, Var?.SSplit.den, Ty.den, Var?.ety,
    ety_var, swap_inner_tensorUnit_right, Category.assoc, Ctx?.den, Ctx?.ety,
    Central.left_exchange_assoc (f := (ρ_ _).inv), distl_inv_naturality_left_assoc,
    addHom_desc, associator_naturality_right_assoc
  ]
  rw [
    <-PremonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_inv_hom,
    PremonoidalCategory.whiskerLeft_id, Category.id_comp, addHom,
    M.drop_tensor, M.drop_unit, tensorHom_def
  ]
  congr 5 <;> premonoidal

theorem uniformLeftHelper {Γc Γl Γm : Ctx? α}
  [hΓc_copy : Γc.copy] [hΓl_copy : Γl.copy] [hΓl_del : Γl.del] [hΓm_del : Γm.del]
  (hΓc : Γc.SSplit Γl Γm) {A B X : Ty α}
  (f : (t⟦Γm.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦X⟧) (g : (t⟦Γl.ety⟧ ⊗ t⟦X⟧ : C) ⟶ t⟦B⟧ ⊕ₒ t⟦X⟧) :
  (((hΓc.den (C := C) ⊗ (λ_ t⟦A⟧).inv)
      ≫ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ (𝟙_ C ⊗ t⟦A⟧)).hom
      ≫ t⟦Γl.ety⟧ ◁ t⟦Γm.ety⟧ ◁ (λ_ t⟦A⟧).hom ≫ (ρ_ t⟦Γl.ety⟧).inv ▷ _)
      ≫ (t⟦Γl.ety⟧ ⊗ 𝟙_ C) ◁ f)
      ≫ Δ_ (Γl.ety.tensor Ty.unit) ▷ t⟦X⟧
      ≫ (α_ _ _ t⟦X⟧).hom
      ≫ (t⟦Γl.ety⟧ ⊗ 𝟙_ C) ◁
          ((t⟦Γl.ety⟧ ◁ !_ Ty.unit) ▷ t⟦X⟧ ≫ (ρ_ t⟦Γl.ety⟧).hom ▷ t⟦X⟧ ≫ g)
      ≫ (∂L _ t⟦B⟧ t⟦X⟧).inv ≫ (!_ (Γl.ety.tensor Ty.unit) ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ 𝟙 _)
  =
  Δ_ Γc.ety ▷ t⟦A⟧ ≫
    pw⟦hΓc.pwk_right_del⟧ ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
    _ ◁ (hΓc.den (C := C) ▷ _ ≫
      (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ t⟦A⟧).hom ≫ t⟦Γl.ety⟧ ◁ f ≫ g) ≫
    (∂L _ _ _).inv ≫
    ((!_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom) ⊕ₕ ((ρ_ _).inv ▷ _))
  := calc
  _ = hΓc.den (C := C) ▷ _
          ≫ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).hom
          ≫ _ ◁ f ≫ Δ_ Γl.ety ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ g
          ≫ (ρ_ _).inv ▷ _
          ≫ (∂L _ t⟦B⟧ t⟦X⟧).inv
          ≫ (!_ (Γl.ety.tensor Ty.unit) ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ 𝟙 _)
    := by
      simp only [M.copy_tensor, M.copy_unit, M.drop_unit, Ty.den, swap_inner_tensorUnit_right]
      premonoidal
  _ = hΓc.den (C := C) ▷ _
          ≫ (α_ t⟦Γl.ety⟧ t⟦Γm.ety⟧ _).hom
          ≫ _ ◁ f ≫ Δ_ Γl.ety ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ g
          ≫ (∂L _ t⟦B⟧ t⟦X⟧).inv
          ≫ (!_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ (ρ_ _).inv ▷ _)
    := by
      simp only [addHom, Category.assoc, Ty.den, M.drop_tensor, M.drop_unit, tensorHom_id,
        PremonoidalCategory.whiskerRight_id, comp_whiskerRight, leftUnitor_whiskerRight,
        triangle_assoc_comp_right_inv_assoc, id_whiskerLeft, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
        Category.comp_id, distl_inv_naturality_left_assoc, desc_comp, inl_desc,
        inv_hom_whiskerRight_assoc, inr_desc, Category.id_comp]
  _ = hΓc.den (C := C) ▷ _ ≫ Δ_ Γl.ety ▷ _ ▷ _ ≫ (α_ _ _ _).hom
          ≫ _ ◁ f ≫ (α_ _ _ _).hom ≫ _ ◁ g
          ≫ (∂L _ t⟦B⟧ t⟦X⟧).inv
          ≫ (!_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ (ρ_ _).inv ▷ _)
    := by rw [<-Central.left_exchange_assoc, <-associator_naturality_left_assoc]
  _ = _ := by
    simp only [<-PremonoidalCategory.comp_whiskerRight_assoc]
    rw [Ctx?.SSplit.den_dup_left_dup_eq_wk]
    simp only [tensorHom_def, Category.assoc]
    premonoidal

theorem uniformRightHelper {Γc Γl Γm : Ctx? α}
  [hΓc_copy : Γc.copy] [hΓc_del : Γc.del] [hΓl_del : Γl.del] [hΓm_del : Γm.del]
  (hΓc : Γc.SSplit Γl Γm) {A B X : Ty α}
  (f : (t⟦Γm.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦X⟧) (g : (t⟦Γc.ety⟧ ⊗ t⟦A⟧ : C) ⟶ t⟦B⟧ ⊕ₒ t⟦A⟧) :
  Δ_ Γc.ety ▷ t⟦A⟧ ≫
      (α_ t⟦Γc.ety⟧ t⟦Γc.ety⟧ t⟦A⟧).hom ≫
        t⟦Γc.ety⟧ ◁ g ≫ (∂L g⟦Γc⟧ t⟦B⟧ t⟦A⟧).inv ≫ (!_ Γc.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ 𝟙 _) ≫
    (𝟙 t⟦B⟧ ⊕ₕ css⟦hΓc.cons (Var?.SSplit.right { ty := A, q := ⊤ })⟧ ≫ g⟦Γl.cons ⟨A, 0⟩⟧ ◁ f) =
  Δ_ Γc.ety ▷ t⟦A⟧ ≫
    pw⟦hΓc.pwk_right_del⟧ ▷ t⟦Γc.ety⟧ ▷ t⟦A⟧ ≫
      (α_ g⟦Γl⟧ t⟦Γc.ety⟧ t⟦A⟧).hom ≫
        g⟦Γl⟧ ◁
            (Δ_ Γc.ety ▷ t⟦A⟧ ≫
              (α_ t⟦Γc.ety⟧ t⟦Γc.ety⟧ t⟦A⟧).hom ≫
                t⟦Γc.ety⟧ ◁ g ≫
                  (∂L t⟦Γc.ety⟧ t⟦B⟧ t⟦A⟧).inv ≫
                    (!_ Γc.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ
                      pw⟦Ctx?.PWk.scons { ty := A, q := ⊤ } hΓc.pwk_left_del⟧ ≫ f)) ≫
          (∂L g⟦Γl⟧ t⟦B⟧ t⟦X⟧).inv ≫ (!_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ (ρ_ g⟦Γl⟧).inv ▷ t⟦X⟧)
  := by
  rw [
    associator_naturality_left_assoc,
    Central.left_exchange_assoc (f := pw⟦_⟧),
    distl_inv_naturality_left_assoc,
    PremonoidalCategory.whiskerLeft_comp_assoc,
    <-associator_naturality_middle_assoc,
    PremonoidalCategory.whiskerLeft_comp_assoc,
    PremonoidalCategory.whiskerLeft_comp_assoc,
    PremonoidalCategory.whiskerLeft_comp_assoc,
    distl_inv_naturality_right_assoc,
    distl_inv_distl_inv_assoc,
    addHom_comp_addHom,
    addHom_comp_addHom,
    addHom_comp_addHom,
    addHom_comp_addHom,
    associator_inv_naturality_right_assoc,
    <-comp_whiskerRight_assoc,
    <-M.copy_assoc,
    Category.comp_id,
    Category.id_comp
  ]
  calc
    _ = _ := by
      congr 5
      · simp only [PremonoidalCategory.whiskerLeft_comp, Category.assoc]
        rw [<-associator_naturality_middle_assoc, <-comp_whiskerRight_assoc, M.copy_drop_right]
        simp only [triangle_assoc, inv_hom_whiskerRight_assoc]
        rw [<-comp_whiskerRight_assoc, M.drop_aff ⊥]
      · simp only [
          Ctx?.PWk.scons, Ctx?.PWk.den, PremonoidalCategory.whiskerLeft_comp, tensorHom_def,
          Category.assoc, Var?.ety, ety_var, Ctx?.SSplit.den, Var?.SSplit.den, Ty.den,
          swap_inner_tensorUnit_right, <-associator_naturality_middle_assoc,
          <-associator_naturality_right_assoc, whiskerLeft_inv_hom_assoc, Ctx?.den, Ctx?.ety,
          Var?.Wk.den_refl, PremonoidalCategory.whiskerLeft_id, Category.id_comp
        ]
        rw [<-Central.left_exchange_assoc, <-associator_naturality_left_assoc (f := pw⟦_⟧)]
        simp only [<-PremonoidalCategory.comp_whiskerRight_assoc]
        congr 2
        · rw [
            <-Ctx?.SSplit.den_both, <-Ctx?.SSplit.den_unstrict, <-Ctx?.SSplit.den_unstrict,
            Ctx?.Split.den_wkOutR_assoc, Ctx?.Split.den_wkOutL
          ]
          apply Ctx?.Split.coherence
        · simp only [Central.left_exchange]
    (Δ_ Γc.ety ▷ t⟦A⟧
      ≫ (α_ _ _ _).hom
      ≫ _ ◁ g
      ≫ (∂L _ t⟦B⟧ t⟦A⟧).inv
      ≫ (
        Δ_ Γc.ety ▷ _
        ≫ (α_ g⟦Γc⟧ t⟦Γc.ety⟧ t⟦B⟧).hom
        ≫ g⟦Γc⟧ ◁ (!_ Γc.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom)
        ≫ pw⟦hΓc.pwk_right_del⟧ ▷ t⟦B⟧
        ≫ !_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ
        Δ_ Γc.ety ▷ _
        ≫ (α_ g⟦Γc⟧ t⟦Γc.ety⟧ t⟦A⟧).hom
        ≫ g⟦Γc⟧ ◁ (pw⟦hΓc.pwk_left_del.scons ⟨A, ⊤⟩⟧ ≫ f)
        ≫ pw⟦hΓc.pwk_right_del⟧ ▷ t⟦X⟧ ≫ (ρ_ g⟦Γl⟧).inv ▷ t⟦X⟧)) = _
      := by rw [Central.left_exchange_assoc, distl_inv_naturality_left_assoc, addHom_comp_addHom]
    (Δ_ Γc.ety ▷ t⟦A⟧
      ≫ (α_ _ _ _).hom
      ≫ Δ_ Γc.ety ▷ _
      ≫ _ ◁ g
      ≫ (∂L _ t⟦B⟧ t⟦A⟧).inv
      ≫ (
        (α_ g⟦Γc⟧ t⟦Γc.ety⟧ t⟦B⟧).hom
        ≫ g⟦Γc⟧ ◁ (!_ Γc.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom)
        ≫ pw⟦hΓc.pwk_right_del⟧ ▷ t⟦B⟧
        ≫ !_ Γl.ety ▷ t⟦B⟧ ≫ (λ_ t⟦B⟧).hom ⊕ₕ
        (α_ g⟦Γc⟧ t⟦Γc.ety⟧ t⟦A⟧).hom
        ≫ g⟦Γc⟧ ◁ (pw⟦hΓc.pwk_left_del.scons ⟨A, ⊤⟩⟧ ≫ f)
        ≫ pw⟦hΓc.pwk_right_del⟧ ▷ t⟦X⟧ ≫ (ρ_ g⟦Γl⟧).inv ▷ t⟦X⟧)) = _
      := by premonoidal

theorem RWS.uniform.ref {R : RWS φ α} [V : R.Valid C] {Γ A a b} (h : uniform R Γ A a b)
  (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) ↠ Db.den := by induction h with
  | base h => apply V.den_ref h
  | refl => apply refines_of_eq; apply Deriv.coherence
  | trans hab hbc I I' => have ⟨Db'⟩ := hbc.wt.left; exact refines_trans (I Da Db') (I' Db' Db)
  | let₁ hΓ ra rb Ia Ib =>
    have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
    have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
    convert_to (Dax.let₁ hΓ Dbx).den (C := C) ↠ (Day.let₁ hΓ Dby).den
    apply Deriv.coherence
    apply Deriv.coherence
    simp only [Deriv.den]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerLeft
    exact Ia Dax Day
    exact Ib Dbx Dby
  | let₂ hΓ ra rb Ia Ib =>
    have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
    have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
    convert_to (Dax.let₂ hΓ Dbx).den (C := C) ↠ (Day.let₂ hΓ Dby).den
    apply Deriv.coherence
    apply Deriv.coherence
    simp only [Deriv.den]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerLeft
    exact Ia Dax Day
    apply refines_comp
    rfl
    exact Ib Dbx Dby
  | pair hΓ ra rb Ia Ib =>
    have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
    have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
    convert_to (Dax.pair hΓ Dbx).den (C := C) ↠ (Day.pair hΓ Dby).den
    apply Deriv.coherence
    apply Deriv.coherence
    simp only [Deriv.den]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerRight
    exact Ia Dax Day
    apply refines_whiskerLeft
    exact Ib Dbx Dby
  | op hf =>
    cases Da with | op hfa => cases Db with | op hfb =>
    cases hf.src; cases hf.trg;
    cases hfa.src; cases hfa.trg;
    cases hfb.src; cases hfb.trg;
    simp only [Deriv.den]
    apply refines_comp
    apply_assumption
    rfl
  | case hΓ ra rb rc Ia Ib Ic =>
    have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left; have ⟨Dcx⟩ := rc.wt.left;
    have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right; have ⟨Dcy⟩ := rc.wt.right;
    convert_to (Dax.case hΓ Dbx Dcx).den (C := C) ↠ (Day.case hΓ Dby Dcy).den
    apply Deriv.coherence
    apply Deriv.coherence
    simp only [Deriv.den]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerLeft
    exact Ia Dax Day
    apply refines_comp
    rfl
    apply refines_desc
    apply Ib
    apply Ic
  | inl | inr | abort =>
    cases Da; cases Db;
    simp only [Deriv.den]
    apply refines_comp
    apply_assumption
    rfl
  | iter hΓ hc hd ra rb Ia Ib =>
    have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
    have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
    convert_to (Dax.iter hΓ hc hd Dbx).den (C := C) ↠ (Day.iter hΓ hc hd Dby).den
    apply Deriv.coherence
    apply Deriv.coherence
    simp only [Deriv.den]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerLeft
    exact Ia Dax Day
    apply refines_iterate
    apply refines_comp
    rfl
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_whiskerLeft
    exact Ib Dbx Dby
    rfl
  | pos_unif hΓ hΓc hc hd hei he Dra ha Dms hs Dlb hb Dcb' rs Ia =>
    stop
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
          (pw⟦hΓc.pwk_left_del.scons ⟨A, ⊤⟩⟧ ≫ Dms.den))
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
        Ctx?.den, Ctx?.ety, Ty.den, Var?.ety_erase, Deriv.den_wk1, Var?.ety, ety_var,
        Ctx?.SSplit.den, Var?.SSplit.den, swap_inner_tensorUnit_right
      ]
      apply uniformLeftHelper
    · simp only [iter_right, hIa_right]
      convert uniformRightHelper (M := M) hΓc Dms.den Dcb'.den using 1
      simp
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
    · simp only [Deriv.den, Deriv.den_wk1]
      apply uniformLeftIndHelper
    · simp only [Deriv.den, Deriv.den_wk1, Deriv.den_pwk, Ctx?.At.den, Var?.Wk.den, eqToHom_refl]
      apply uniformRightIndHelper
    rfl
  | neg_unif hΓ hΓc hc hd hei he Dra ha Dms hs Dlb hb Dcb' rs Ia =>
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
          (pw⟦hΓc.pwk_left_del.scons ⟨A, ⊤⟩⟧ ≫ Dms.den))
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
    · simp only [iter_right, hIa_right]
      convert uniformRightHelper (M := M) hΓc _ _ using 1
      simp
    · simp only [
        Ctx?.den, Ctx?.ety, Ty.den, Var?.ety_erase, Deriv.den_wk1, Var?.ety, ety_var,
        Ctx?.SSplit.den, Var?.SSplit.den, swap_inner_tensorUnit_right
      ]
      apply uniformLeftHelper
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
    · simp only [Deriv.den, Deriv.den_wk1, Deriv.den_pwk, Ctx?.At.den, Var?.Wk.den, eqToHom_refl]
      apply uniformRightIndHelper
    · simp only [Deriv.den, Deriv.den_wk1]
      apply uniformLeftIndHelper
    rfl

instance RWS.uniform_valid (R : RWS φ α) [V : R.Valid C] : R.uniform.Valid C where
  den_ref := RWS.uniform.ref

theorem DRWS.uniform.ref {R : DRWS φ α} [V : R.Valid C] {Γ A a b}
  (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) (h : (uniform R).rel Da Db) : Da.den (C := C) ↠ Db.den
  := by
  have h : (uniform R).toRWS Γ A a b := ⟨Da, Db, h⟩;
  rw [DRWS.toRWS_uniform] at h
  apply RWS.Valid.den_ref h _ _

instance DRWS.uniform_valid (R : DRWS φ α) [V : R.Valid C] : R.uniform.Valid C where
  den_ref := DRWS.uniform.ref
