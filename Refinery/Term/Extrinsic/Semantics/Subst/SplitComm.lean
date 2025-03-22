import Refinery.Term.Extrinsic.Semantics.Subst.Basic

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]


inductive SubstDS.CommEff
  (C : Type _) [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
  [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]
  : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
  | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : CommEff C e (.nil hΓ)
  | cons {e el er} {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
    (hσ : σ.CommEff C el) (ha : da.HasEff er)
    (hl : el ≤ e) (hr : er ≤ e) (hcomm : el ⇌ er)
    (hcopy : v.copy ->
      ∀{A B : Ty α} [IsRel A],
      ∀f : (t⟦A⟧ : C) ⟶ t⟦B⟧, [E.HasEff er f] → Δ_ A ≫ f ⋉ f = Δ_ A ≫ f ⋊ f
    )
    : CommEff C e (σ.cons hΓ da)

variable {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

theorem SubstDS.CommEff.mono
  {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} {σ : SubstDS φ Γ Δ} (h : σ.CommEff C e)
  : σ.CommEff C e' := by
  induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm hq =>
    constructor; apply_assumption; assumption
    apply le_trans <;> assumption; apply le_trans <;> assumption; assumption
    assumption

theorem SubstDS.CommEff.has_eff
  (e : ε) {Γ Δ : Ctx? α} {σ : SubstDS φ Γ Δ} (h : σ.CommEff C e)
  : σ.HasEff e := by induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ => constructor; exact Iσ.mono hl; exact ha.mono hr


theorem SubstDS.CommEff.den_eq_den'_split (e : ε) {Γ Δ : Ctx? α} {σ : SubstDS φ Γ Δ}
  (hσ : σ.CommEff C e) {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).den (C := C) = (σ.ssplit hΔ).den' (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      SubstDS.ssplit, SubstSSplit.den_eq_ltimes, SubstSSplit.den', SubstDS.den,
      SubstSSplit.erase_left, left_exchange]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    have hσ' := hσ.has_eff;
    rename_i v a e el er Γ Γl Γr Δ
    simp only [SubstSSplit.den, SubstSSplit.den'] at Iσ
    have Iσ_assoc : ∀ {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
      {Y : C} {f : ((g⟦Δl⟧ : C) ⊗ g⟦Δr⟧) ⟶ Y},
      css⟦(σ.ssplit hΔ).ssplitIn⟧
        ≫ ((σ.ssplit hΔ).substLeft.den (C := C) ⊗ (σ.ssplit hΔ).substRight.den) ≫ f =
      css⟦(σ.ssplit hΔ).ssplitIn⟧
        ≫ _ ◁ (σ.ssplit hΔ).substRight.den
        ≫ (σ.ssplit hΔ).substLeft.den ▷ g⟦Δr⟧
        ≫ f
        := by
          intros; rw [<-Category.assoc, <-Category.assoc, <-Category.assoc, Iσ]
          simp only [Category.assoc]
    cases hΔ with | cons hΔ hlr => cases hlr with
    | left =>
      simp only [SubstDS.ssplit, SubstSSplit.den_eq_ltimes, SubstSSplit.den']
      if hv : v.used then
        rw [dite_cond_eq_true (by simp [hv])]
        simp only [
          SubstDS.den, Deriv?.den_zero, Ctx?.SSplit.den_drop_tensor_right, Ctx?.PWk.den_refl',
          Category.id_comp
        ]
        simp only [
          comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp, Category.assoc, tensorHom_def,
          <-left_exchange_assoc, Ty.den, Ctx?.den, Ctx?.ety,
        ]
        simp only [
          Ctx?.SSplit.den_comm, Ctx?.SSplit.den_s12_3_1_23_assoc, Category.assoc,
          <-BraidedCategory'.braiding_naturality_right_assoc,
          <-BraidedCategory'.braiding_naturality_left_assoc,
          <-BraidedCategory'.braiding_naturality_right,
          <-BraidedCategory'.braiding_naturality_left,
          comp_whiskerRight_assoc,
        ]
        calc
        _ = css⟦hΓ⟧
          ≫ css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ ((β'_ _ _).hom ≫ _ ◁ (σ.ssplit hΔ).substLeft.den) ▷ _
          ≫ _ ◁ da.den
          ≫ (σ.ssplit hΔ).substRight.den ▷ _ ▷ _
          ≫ (α_ _ _ _).hom
          ≫ (ρ_ _).inv ▷ _
          ≫ (β'_ _ _).hom
          := by premonoidal
        _ = css⟦hΓ⟧
          ≫ css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ (σ.ssplit hΔ).substLeft.den ▷ _ ▷ _
          ≫ _ ◁ da.den
          ≫ (_ ◁ (σ.ssplit hΔ).substRight.den ≫ (β'_ _ _).hom) ▷ _
          ≫ (α_ _ _ _).hom
          ≫ (ρ_ _).inv ▷ _
          ≫ (β'_ _ _).hom
          := by rw [
              <-BraidedCategory'.braiding_naturality_left, comp_whiskerRight_assoc,
              left_exchange_assoc, BraidedCategory'.braiding_naturality_right,
              comp_whiskerRight_assoc
            ]
        _ = css⟦hΓ⟧
          ≫ (css⟦(σ.ssplit hΔ).ssplitIn⟧
            ≫ (σ.ssplit hΔ).substLeft.den ▷ _
            ≫ (_ ◁ (σ.ssplit hΔ).substRight.den)) ▷ _
          ≫ _ ◁ da.den
          ≫ (β'_ _ _).hom ▷ _
          ≫ (α_ _ _ _).hom
          ≫ (ρ_ _).inv ▷ _
          ≫ (β'_ _ _).hom
          := by
            rw [comp_whiskerRight_assoc, <-whiskerLeft_swap_of_swap_assoc]
            premonoidal
            rw [E.eff_comm_exchange hcomm]
        _ = css⟦hΓ⟧
          ≫ css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ ((_ ◁ (σ.ssplit hΔ).substRight.den)
            ≫ (σ.ssplit hΔ).substLeft.den ▷ _
            ≫ (β'_ _ _).hom) ▷ _
          ≫ _ ◁ da.den
          ≫ (α_ _ _ _).hom
          ≫ (ρ_ _).inv ▷ _
          ≫ (β'_ _ _).hom
          := by rw [<-tensorHom_def, Iσ, <-left_exchange_assoc]; premonoidal
        _ = _ := by
          rw [braiding_naturality_left, braiding_naturality_right_assoc]
          premonoidal
      else
        rw [dite_cond_eq_false (by simp [hv])]
        cases v using Var?.casesZero with
        | zero =>
          simp only [
            Deriv?.unused, SubstDS.den, Ty.den, Deriv?.den_zero', Ctx?.PWk.den_refl',
            Ctx?.SSplit.den_drop_tensor_right, Category.id_comp, Ctx?.den, Ty.den, Ctx?.ety,
          ]
          simp only [
            PremonoidalCategory.whiskerLeft_comp, Category.assoc, tensorHom_def,
            right_exchange_assoc, <-right_exchange
          ]
          simp only [
            Ctx?.SSplit.den_s12_3_1_23_assoc,
            <-associator_naturality_middle_assoc, <-associator_naturality_left_assoc,
            <-comp_whiskerRight_assoc,
          ]
          rw [
            comp_whiskerRight_assoc (g := (ρ_ _).inv), left_exchange, <-tensorHom_def_assoc,
            Iσ_assoc
          ]
          premonoidal
        | rest => simp at hv
    | right =>
      simp only [
        SubstDS.ssplit, Ctx?.den, Ctx?.ety, Ty.den, SubstSSplit.den, SubstSSplit.den', SubstDS.den,
        Deriv?.den_zero', Ctx?.SSplit.den_drop_tensor_right, Ctx?.PWk.den_refl', Category.id_comp,
      ]
      simp only [
        PremonoidalCategory.whiskerLeft_comp, Category.assoc, tensorHom_def,
        right_exchange_assoc, <-right_exchange, Category.assoc,
      ]
      simp only [
        Ctx?.SSplit.den_s12_3_1_23_assoc,
        <-associator_naturality_middle_assoc, <-associator_naturality_left_assoc,
        <-associator_naturality_right_assoc, <-comp_whiskerRight_assoc,
      ]
      rw [
        comp_whiskerRight_assoc (g := (ρ_ _).inv), left_exchange, <-tensorHom_def_assoc,
        Iσ_assoc
      ]
      simp only [
        PremonoidalCategory.whiskerLeft_comp, PremonoidalCategory.whiskerLeft_comp_assoc,
        comp_whiskerRight, comp_whiskerRight_assoc,
        <-associator_naturality_left_assoc,
      ]
      rw [<-E.eff_comm_exchange_assoc hcomm (f := _) (g := da.den)]
      premonoidal
    | sboth hvc =>
      simp only [SubstDS.ssplit]
      if hv : v.used then
        rw [dite_cond_eq_true (by simp [hv]), SubstSSplit.den, SubstSSplit.den']
        simp only [SubstDS.den, tensor_comp_of_right]
        rw [Ctx?.SSplit.den_s12_34_13_24_assoc, comp_whiskerRight]
        simp only [<-left_exchange_assoc]
        rw [
          PremonoidalCategory.whiskerLeft_comp_assoc, <-tensorHom_def_assoc,
          Ctx?.SSplit.den_s12_34_13_24_assoc
        ]
        simp only [tensorHom_def, comp_whiskerRight, Category.assoc,
          PremonoidalCategory.whiskerLeft_comp, <-swap_inner_naturality_outer_left_assoc,
          <-swap_inner_naturality_right_assoc, <-swap_inner_naturality_left_assoc, Ctx?.den,
          Ty.den, Ctx?.ety, <-swap_inner_naturality_outer_right_assoc,
          <-swap_inner_naturality_right, <-swap_inner_naturality_outer_right,
          Ctx?.SSplit.den_both]
        rw [
          <-E.eff_comm_exchange_assoc hcomm (f := _) (g := da.den ▷ _),
          <-E.eff_comm_exchange_assoc hcomm (f := _) (g := _ ◁ da.den),
        ]
        simp only [<-right_exchange_assoc]
        simp only [<-comp_whiskerRight_assoc]
        rw [<-tensorHom_def, Iσ]
        congr 2
        simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc]
        rw [<-ltimes, <-rtimes]
        have _ : Γr.copy := da.copy hv hvc.copy;
        rw [hq hvc.copy]
      else
        cases v using Var?.casesZero with
        | zero =>
          rw [dite_cond_eq_false (by simp [hv]), SubstSSplit.den, SubstSSplit.den']
          simp only [Deriv?.unused, SubstDS.den, Ty.den, Deriv?.den_zero',
            Ctx?.SSplit.den_drop_tensor_right, Ctx?.PWk.den_refl', Category.id_comp,
            PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc
          ]
          simp only [tensorHom_def, comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp,
            Category.assoc, right_exchange_assoc, Ctx?.SSplit.den_s12_3_1_23_assoc,
            <-associator_naturality_middle_assoc, <-associator_naturality_right_assoc,
            <-associator_naturality_left_assoc, Ctx?.den, Ctx?.ety, Ty.den
          ]
          simp only [<-comp_whiskerRight_assoc]
          rw [<-Iσ, <-right_exchange_assoc, tensorHom_def]
          premonoidal
        | rest => simp at hv
