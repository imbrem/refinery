import Refinery.Term.Extrinsic.Subst.Effect
import Refinery.Term.Extrinsic.Semantics.Wk
import Refinery.Term.Extrinsic.Semantics.Effect
import Refinery.Ctx.Semantics.SplitWk
import Refinery.Ctx.Semantics.Coherence

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory ChosenFiniteCoproducts
      HasQuant HasCommRel EffectfulCategory BraidedCategory' SymmetricCategory'

open scoped MonoidalCategory

namespace Term

section BraidedCategory

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PC : PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

def Deriv?.den {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} : (Γ ⊢? a : v) → ((g⟦Γ⟧ : C) ⟶ v⟦v⟧)
  | .valid _ _ D hΓ => D.den
  | .zero hΓ a A => !_ _

@[simp]
theorem Deriv?.den_valid {Γ : Ctx? α} {A : Ty α} {q : Quant} {a : Term φ (Ty α)} (D : Γ ⊢ a : A)
  (hΓ : quant (Var?.mk A q) ≤ quant Γ)
  : (Deriv?.valid A q D hΓ).den (C := C) = D.den
  := rfl

theorem Deriv?.den_zero {Γ : Ctx? α} [hΓ : Γ.del] {a : Term φ (Ty α)} {A : Ty α}
  : (Deriv?.zero hΓ a A).den (C := C) = !_ _
  := rfl

@[simp]
theorem Deriv?.den_zero' {Γ : Ctx? α} {a : Term φ (Ty α)} {A : Ty α}
  (da : Γ ⊢? a : ⟨A, 0⟩) : da.den (C := C) = haveI _ : Γ.del := da.del_of_unused (by simp); !_ _
  := by cases da; rfl

@[simp]
instance Deriv?.den_eff (e : ε) {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (D : Γ ⊢? a : v)
  [hD : D.HasEff e]
  : E.HasEff e D.den := by cases hD <;> simp only [Deriv?.den] <;> infer_instance

def SubstDS.den {Γ Δ : Ctx? α} : (σ : SubstDS φ Γ Δ) → ((g⟦Γ⟧ : C) ⟶ g⟦Δ⟧)
  | .nil hΓ => !_ _
  | .cons hΓ σ da => hΓ.den ≫ (σ.den ⊗ da.den)

@[simp]
instance SubstDS.den_eff (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.HasEff e]
  : E.HasEff e σ.den := by induction hσ <;> simp only [SubstDS.den] <;> infer_instance

@[simp]
theorem Deriv?.den_bv0 (Γ : Ctx? α) (v : Var? α)
  : (Deriv?.bv0 Γ v).den (C := C) = !_ Γ.erase.ety ▷ _ ≫ (λ_ _).hom
  := by cases v using Var?.casesZero <;> simp [Deriv?.bv0, Deriv?.den, M.drop_tensor]

theorem Deriv?.den_wk {Γ Δ : Ctx? α}
  (ρ : Γ.Wk Δ) (h : quant Δ ≤ quant Γ) {v : Var? α} (D : Δ ⊢? a : v)
  : (D.wk ρ h).den (C := C) = ρ.den ≫ D.den
  := by cases D <;> simp [Deriv?.den, Deriv?.wk, Deriv.den_wk]

@[reassoc]
theorem SubstDS.den_wkIn {Γ' Γ Δ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : SubstDS φ Γ Δ)
  : (σ.wkIn ρ).den (C := C) = ρ.den ≫ σ.den
  := by induction σ generalizing Γ' with
  | nil => simp [wkIn, den]
  | cons =>
    simp only [wkIn, den, Deriv?.den_wk, tensorHom_def, comp_whiskerRight,
      PremonoidalCategory.whiskerLeft_comp, Category.assoc, Central.right_exchange_assoc, *]
    rw [<-tensorHom_def_of_left_assoc, <-Ctx?.SSplit.wk_den'_assoc]

theorem SubstDS.den_lift {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v : Var? α)
  : (σ.lift v).den (C := C) = σ.den ▷ _
  := by
  simp only [
    lift, den, Deriv?.den_bv0, tensorHom_def_of_right, den_wkIn, Ctx?.Wk.den, Ctx?.wk0,
    Ctx?.Wk.den_refl, id_whiskerRight, Category.comp_id,
    Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
    swap_inner_tensorUnit_right,
    PremonoidalCategory.whiskerLeft_comp, Var?.del.den_unused, eqToHom_refl,
    PremonoidalCategory.whiskerLeft_id, Category.assoc, comp_whiskerRight
  ]
  calc
      _ = (css⟦Γ.erase_right⟧ ≫ _ ◁ !_ Γ.erase.ety ≫ (ρ_ _).hom) ▷ _ ≫ σ.den ▷ _
        := by premonoidal
      _ = _
        := by rw [Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl']; simp

def SubstSSplit.den {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : (g⟦Γ⟧ : C) ⟶ g⟦Δl⟧ ⊗ g⟦Δr⟧
  := σ.ssplitIn.den ≫ (σ.substLeft.den ⊗ σ.substRight.den)

theorem SubstSSplit.den_eq_ltimes {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : σ.den (C := C) = σ.ssplitIn.den ≫ σ.substLeft.den ▷ _ ≫ _ ◁ σ.substRight.den
  := by simp [den, tensorHom_def]

def SubstSSplit.den' {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  : (g⟦Γ⟧ : C) ⟶ g⟦Δl⟧ ⊗ g⟦Δr⟧
  := σ.ssplitIn.den ≫ _ ◁ σ.substRight.den ≫ σ.substLeft.den ▷ _

def SubstSSplit.den_left {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  := σ.substLeft.den (C := C) ▷ _ ≫ _ ◁ σ.substRight.den

def SubstSSplit.den_right {Γ Δ Δl Δr : Ctx? α} (σ : SubstSSplit φ Γ Δ Δl Δr)
  := _ ◁ σ.substRight.den (C := C) ≫ σ.substLeft.den ▷ _

end BraidedCategory

section SymmetricCategory

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

--TODO: need validity here to commute `da` with the subst components...
theorem SubstDS.den_ssplit_pos (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↠ (σ.ssplit hΔ).den (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      ssplit, SubstSSplit.erase_left, SubstSSplit.den, den, tensorHom_def,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl'
    ]
    rw [leftUnitor_inv_naturality]; rfl
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hΔ with
  | cons hΔ hlr =>
  simp only [den, tensorHom_def, Category.assoc, Ctx?.SSplit.den]
  rw [<-Central.left_exchange_assoc, <-comp_whiskerRight_assoc]
  have Iσ' :
    css⟦hΓ⟧
    ≫ (σ.den (C := C) ≫ css⟦hΔ⟧) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    ↠ css⟦hΓ⟧
    ≫ (σ.ssplit hΔ).den (C := C) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    := by apply refines_comp; rfl; apply refines_comp; apply refines_whiskerRight; apply Iσ; rfl
  apply refines_trans Iσ'
  cases hlr with
  | left =>
    apply refines_of_eq; apply Eq.symm
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_left,
      Category.assoc]
    split
    case isTrue h =>
      simp only [SubstSSplit.den, den, tensorHom_def, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc, <-Ctx?.SSplit.den_braiding,
        <-BraidedCategory'.braiding_naturality_right_assoc
      ]
      rw [
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn.comm)
      ]
      congr 1
      simp only [← Ctx?.SSplit.den_braiding, comp_whiskerRight,
        BraidedCategory'.braiding_naturality_right_assoc, BraidedCategory'.braiding_tensor_right,
        Category.assoc, Iso.inv_hom_id_assoc, Deriv?.den_zero, Iso.hom_inv_id_assoc,
        associator_inv_naturality_middle_assoc]
      rw [Central.right_exchange_assoc, E.eff_comm_exchange_assoc hcomm.symm]
      calc
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ ((β'_ _ _).hom
            ≫ (_ ◁ (σ.ssplit hΔ).substLeft.den)
            ≫ (β'_ _ _).hom) ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ (β'_ _ _).hom
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (css⟦(σ.ssplit hΔ).inRight.erase_right⟧
            ≫ _ ◁ !_ (σ.ssplit hΔ).inRight.erase.ety)
          ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ▷ _
          ≫ (_ ◁ da.den) ▷ _ := by
            rw [right_exchange (g := _ ◁ !_ _)]
            simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
            rw [<-right_exchange (g := !_ _)]
            premonoidal
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ (σ.ssplit hΔ).substLeft.den ▷ _ ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ ((β'_ _ _).hom ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ≫ da.den ▷ _)
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (ρ_ _).inv := by
            simp only [
              BraidedCategory'.braiding_naturality_right, SymmetricCategory'.symmetry_assoc,
              Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl', Category.id_comp
            ]
            premonoidal
        _ = _ := by
          congr 2
          rw [
            <-BraidedCategory'.braiding_naturality_left_assoc,
            <-BraidedCategory'.braiding_naturality_right,
          ]
          simp only [swap_inner, assoc_inner]
          premonoidal
    case isFalse h => cases v using Var?.casesZero with
    | zero =>
      simp only [
        SubstSSplit.den, den, tensorHom_def, Ty.den, Deriv?.unused, Deriv?.den_zero',
        right_exchange (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, Ctx?.den, Ctx?.ety, swap_inner_tensorUnit_right
      ]
      simp only [PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight_assoc]
      rw [
        right_exchange_assoc, right_exchange_assoc,
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn)
      ]
      premonoidal
    | rest => simp at h
  | right =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
      Category.assoc, swap_inner_tensorUnit_right, SubstSSplit.den, Deriv?.den_zero,
      tensorHom_def_of_right, Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
      Category.id_comp, tensor_comp_of_right
    ]
    rw [
      <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn),
    ]
    simp only [tensorHom_def]
    premonoidal
  | sboth hv =>
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_sboth,
      Category.assoc]
    split
    case isTrue hv' =>
      have hv : v.copy := hv.copy
      have hΓ : Γr.copy := da.copy hv' hv
      simp only [SubstSSplit.den, den, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      ]
      rw [tensor_comp_of_right, Ctx?.SSplit.den_s12_34_13_24_assoc, tensorHom_def_assoc]
      apply refines_comp; rfl
      apply refines_comp; rfl
      simp only [
        tensorHom_def, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
        Iso.inv_hom_id_assoc, Ctx?.den, Ty.den, Ctx?.ety, Ctx?.SSplit.den_both,
        <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right_assoc,
        <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right
      ]
      rw [<-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-E.eff_comm_exchange_assoc hcomm, <-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-Category.assoc, <-Category.assoc, <-Category.assoc]
      rw [
        Category.assoc,
        <-PremonoidalCategory.whiskerLeft_comp_assoc,
        <-PremonoidalCategory.whiskerLeft_comp,
        <-PremonoidalCategory.whiskerLeft_comp,
        -- Category.assoc,
        -- <-tensorHom_def, <-M.copy_rel_tensor er _ (hf := sorry)
      ]
      apply refines_comp _ (by rfl)
      apply refines_whiskerLeft
      apply refines_trans
      apply M.copy_dup_ltimes er _ (hf := IsDup.of_copy_le_pos (le_trans hv.copy_le_quant hq))
      apply refines_of_eq
      simp [ltimes]
    case isFalse h =>
    cases v using Var?.casesZero with
    | zero =>
      apply refines_of_eq
      have hΓr : Γr.del := da.del (by simp)
      simp only [
        SubstSSplit.den, Deriv?.den_zero', den, Var?.ety, ety_var, M.copy_unit, Ty.den,
        swap_inner_tensorUnit_right, Category.assoc, Ctx?.den, Ctx?.ety, Var?.ety, ety_var
      ]
      rw [
        tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc,
        right_exchange_assoc, Ctx?.SSplit.den_drop_right_assoc, <-rightUnitor_inv_naturality_assoc,
        Category.assoc, Ctx?.SSplit.pwk_den_assoc, tensorHom_def (f := _ ≫ _),
        PremonoidalCategory.whiskerLeft_comp, right_exchange_assoc,
        <-Ctx?.SSplit.den_unstrict, Ctx?.Split.den_wkOut_assoc, <-Ctx?.SSplit.den_unstrict,
        Ctx?.Split.den_wkOutR_assoc, tensorHom_def
      ]
      congr 1
      apply Ctx?.Split.coherence
      premonoidal
    | rest => simp at h

theorem SubstDS.den_ssplit_neg (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den ↞ (σ.ssplit hΔ).den (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ
    simp [
      ssplit, SubstSSplit.erase_left, SubstSSplit.den, den, tensorHom_def,
      Ctx?.SSplit.den_drop_left_assoc, Ctx?.PWk.den_refl'
    ]
    rw [leftUnitor_inv_naturality]; rfl
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hΔ with
  | cons hΔ hlr =>
  simp only [den, tensorHom_def, Category.assoc, Ctx?.SSplit.den]
  rw [<-Central.left_exchange_assoc, <-comp_whiskerRight_assoc]
  have Iσ' :
    css⟦hΓ⟧
    ≫ (σ.den (C := C) ≫ css⟦hΔ⟧) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    ↞ css⟦hΓ⟧
    ≫ (σ.ssplit hΔ).den (C := C) ▷ _
    ≫ _ ◁ da.den ≫ _ ◁ vss⟦hlr⟧ ≫ (βi_ _ _ _ _).hom
    := by apply refines_comp; rfl; apply refines_comp; apply refines_whiskerRight; apply Iσ; rfl
  apply refines_trans _ Iσ'
  cases hlr with
  | left =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_left,
      Category.assoc]
    split
    case isTrue h =>
      simp only [SubstSSplit.den, den, tensorHom_def, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc, <-Ctx?.SSplit.den_braiding,
        <-BraidedCategory'.braiding_naturality_right_assoc
      ]
      rw [
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn.comm)
      ]
      congr 1
      simp only [← Ctx?.SSplit.den_braiding, comp_whiskerRight,
        BraidedCategory'.braiding_naturality_right_assoc, BraidedCategory'.braiding_tensor_right,
        Category.assoc, Iso.inv_hom_id_assoc, Deriv?.den_zero, Iso.hom_inv_id_assoc,
        associator_inv_naturality_middle_assoc]
      rw [Central.right_exchange_assoc, E.eff_comm_exchange_assoc hcomm.symm]
      calc
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ ((β'_ _ _).hom
            ≫ (_ ◁ (σ.ssplit hΔ).substLeft.den)
            ≫ (β'_ _ _).hom) ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ (β'_ _ _).hom
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (css⟦(σ.ssplit hΔ).inRight.erase_right⟧
            ≫ _ ◁ !_ (σ.ssplit hΔ).inRight.erase.ety)
          ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ▷ _
          ≫ (_ ◁ da.den) ▷ _ := by
            rw [right_exchange (g := _ ◁ !_ _)]
            simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
            rw [<-right_exchange (g := !_ _)]
            premonoidal
        _ = css⟦(σ.ssplit hΔ).ssplitIn⟧ ▷ _
          ≫ (σ.ssplit hΔ).substLeft.den ▷ _ ▷ _
          ≫ (α_ _ _ _).hom
          ≫ _ ◁ ((β'_ _ _).hom ≫ _ ◁ (σ.ssplit hΔ).substRight.den (C := C) ≫ da.den ▷ _)
          ≫ (α_ _ _ _).inv
          ≫ _ ◁ (ρ_ _).inv := by
            simp only [
              BraidedCategory'.braiding_naturality_right, SymmetricCategory'.symmetry_assoc,
              Ctx?.SSplit.den_drop_right, Ctx?.PWk.den_refl', Category.id_comp
            ]
            premonoidal
        _ = _ := by
          congr 2
          rw [
            <-BraidedCategory'.braiding_naturality_left_assoc,
            <-BraidedCategory'.braiding_naturality_right,
          ]
          simp only [swap_inner, assoc_inner]
          premonoidal
    case isFalse h => cases v using Var?.casesZero with
    | zero =>
      simp only [
        SubstSSplit.den, den, tensorHom_def, Ty.den, Deriv?.unused, Deriv?.den_zero',
        right_exchange (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, Ctx?.den, Ctx?.ety, swap_inner_tensorUnit_right
      ]
      simp only [PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight_assoc]
      rw [
        right_exchange_assoc, right_exchange_assoc,
        <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn)
      ]
      premonoidal
    | rest => simp at h
  | right =>
    apply refines_of_eq
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_right,
      Category.assoc, swap_inner_tensorUnit_right, SubstSSplit.den, Deriv?.den_zero,
      tensorHom_def_of_right, Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
      Category.id_comp, tensor_comp_of_right
    ]
    rw [
      <-Ctx?.SSplit.assoc_coherence_assoc (σ123_12_3 := hΓ) (σ12 := (σ.ssplit hΔ).ssplitIn),
    ]
    simp only [tensorHom_def]
    premonoidal
  | sboth hv =>
    simp only [ssplit, den, Ctx?.SSplit.den, Ty.den, Var?.SSplit.den_sboth,
      Category.assoc]
    split
    case isTrue hv' =>
      have hv : v.copy := hv.copy
      have hΓ : Γr.copy := da.copy hv' hv
      simp only [SubstSSplit.den, den, Ty.den, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, Category.assoc,
      ]
      rw [tensor_comp_of_right, Ctx?.SSplit.den_s12_34_13_24_assoc, tensorHom_def_assoc]
      apply refines_comp; rfl
      apply refines_comp; rfl
      simp only [
        tensorHom_def, comp_whiskerRight, Category.assoc, PremonoidalCategory.whiskerLeft_comp,
        Iso.inv_hom_id_assoc, Ctx?.den, Ty.den, Ctx?.ety, Ctx?.SSplit.den_both,
        <-swap_inner_naturality_outer_left_assoc, <-swap_inner_naturality_right_assoc,
        <-swap_inner_naturality_left_assoc, <-swap_inner_naturality_outer_right
      ]
      rw [<-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-E.eff_comm_exchange_assoc hcomm, <-Central.right_exchange_assoc]
      apply refines_comp; rfl
      rw [<-Category.assoc, <-Category.assoc, <-Category.assoc]
      rw [
        Category.assoc,
        <-PremonoidalCategory.whiskerLeft_comp,
        <-PremonoidalCategory.whiskerLeft_comp,
        <-PremonoidalCategory.whiskerLeft_comp_assoc,
        Category.assoc,
      ]
      apply refines_comp _ (by rfl)
      apply refines_whiskerLeft
      apply refines_trans
      apply M.copy_fuse_ltimes er da.den
        (hf := IsFuse.of_copy_le_neg (le_trans hv.copy_le_quant hq));
      apply refines_of_eq
      simp [ltimes]
    case isFalse h =>
    cases v using Var?.casesZero with
    | zero =>
      apply refines_of_eq; apply Eq.symm
      have hΓr : Γr.del := da.del (by simp)
      simp only [
        SubstSSplit.den, Deriv?.den_zero', den, Var?.ety, ety_var, M.copy_unit, Ty.den,
        swap_inner_tensorUnit_right, Category.assoc, Ctx?.den, Ctx?.ety, Var?.ety, ety_var
      ]
      rw [
        tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl',
        Category.id_comp, tensorHom_def_of_right (g := !_ _), Ctx?.SSplit.den_drop_right_assoc,
        right_exchange_assoc, Ctx?.SSplit.den_drop_right_assoc, <-rightUnitor_inv_naturality_assoc,
        Category.assoc, Ctx?.SSplit.pwk_den_assoc, tensorHom_def (f := _ ≫ _),
        PremonoidalCategory.whiskerLeft_comp, right_exchange_assoc,
        <-Ctx?.SSplit.den_unstrict, Ctx?.Split.den_wkOut_assoc, <-Ctx?.SSplit.den_unstrict,
        Ctx?.Split.den_wkOutR_assoc, tensorHom_def
      ]
      congr 1
      apply Ctx?.Split.coherence
      premonoidal
    | rest => simp at h

theorem SubstDS.den_ssplit_pos_tensor (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↠ (σ.ssplitIn hΔ).den (C := C) ≫ ((σ.substLeft hΔ).den ⊗ (σ.substRight hΔ).den)
  := σ.den_ssplit_pos e hΔ

theorem SubstDS.den_ssplit_neg_tensor (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↞ (σ.ssplitIn hΔ).den (C := C) ≫ ((σ.substLeft hΔ).den ⊗ (σ.substRight hΔ).den)
  := σ.den_ssplit_neg e hΔ

theorem SubstDS.den_ssplit_pos_left (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↠ (σ.ssplitIn hΔ).den (C := C) ≫ (σ.substLeft hΔ).den ▷ _ ≫ _ ◁ (σ.substRight hΔ).den
  := by convert σ.den_ssplit_pos_tensor e hΔ; simp only [tensorHom_def]

theorem SubstDS.den_ssplit_neg_left (e : ε) {Γ Δ : Ctx? α}
  (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : σ.den ≫ hΔ.den
  ↞ (σ.ssplitIn hΔ).den (C := C) ≫ (σ.substLeft hΔ).den ▷ _ ≫ _ ◁ (σ.substRight hΔ).den
  := by convert σ.den_ssplit_neg_tensor e hΔ; simp only [tensorHom_def]

theorem SubstDS.den_drop_pos (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] [hΔ : Δ.del]
  : σ.den (C := C) ≫ !_ Δ.ety ↠ (haveI _ : Γ.del := σ.del; !_ Γ.ety)
  := by
  generalize hΔ = hΔ
  induction hσ with
  | nil => simp [den, Ty.den, Ctx?.den]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i v a e el er Γ Γl Γr Δ
    have hv := hΔ.head
    have hΔ : Δ.del := hΔ.tail;
    have hΓl := σ.del;
    have hΓr := da.del hv;
    have hΓd := hΓ.in_del
    simp [den, Ty.den, Ctx?.den, M.drop_tensor]
    rw [<-tensor_comp_of_left_assoc]
    have hΓ : !_ Γ.ety
      = hΓ.den (C := C) ≫ (PremonoidalCategory.tensorHom (!_ Γl.ety) (!_ Γr.ety)) ≫ (λ_ _).hom
      := by rw [<-M.drop_tensor, M.drop_aff ⊥ (B := Γl.ety.tensor Γr.ety)]
    rw [hΓ]
    apply refines_comp; rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ hΔ
    apply M.drop_rem er (f := da.den) (hf := IsRem.of_del_le_pos (le_trans hv.del_le_quant hq))
    rfl

theorem SubstDS.den_drop_neg (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] [hΔ : Δ.del]
  : σ.den (C := C) ≫ !_ Δ.ety ↞ (haveI _ : Γ.del := σ.del; !_ Γ.ety)
  := by
  generalize hΔ = hΔ
  induction hσ with
  | nil => simp [den, Ty.den, Ctx?.den]
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
    rename_i v a e el er Γ Γl Γr Δ
    have hv := hΔ.head
    have hΔ : Δ.del := hΔ.tail;
    have hΓl := σ.del;
    have hΓr := da.del hv;
    have hΓd := hΓ.in_del
    simp [den, Ty.den, Ctx?.den, M.drop_tensor]
    rw [<-tensor_comp_of_left_assoc]
    have hΓ : !_ Γ.ety
      = hΓ.den (C := C) ≫ (PremonoidalCategory.tensorHom (!_ Γl.ety) (!_ Γr.ety)) ≫ (λ_ _).hom
      := by rw [<-M.drop_tensor, M.drop_aff ⊥ (B := Γl.ety.tensor Γr.ety)]
    rw [hΓ]
    apply refines_comp; rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ hΔ
    apply M.drop_add er (f := da.den) (hf := IsAdd.of_del_le_neg (le_trans hv.del_le_quant hq))
    rfl

theorem SubstDS.den_at_pos
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Pos e] {A} {q : Quant} (hv : Δ.At ⟨A, q⟩ n)
  : σ.den ≫ hv.den ↠ (σ.at hv).den (C := C) := by induction hσ generalizing n with
  | nil => cases hv
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hv with
  | here hd hv =>
    cases da with
    | zero => simp at hv
    | valid A' q da hq' =>
      have hΓl := σ.del;
      cases hv.ty
      simp only [«at», Deriv.cast_rfl, Deriv.den_pwk, den, Var?.ety, ety_var, Deriv?.den_valid,
        tensorHom_def, Ctx?.At.den, ge_iff_le, EQuant.one_le_coe, Var?.Wk.den_used, eqToHom_refl,
        PremonoidalCategory.whiskerLeft_id, Category.comp_id, Category.assoc, ← left_exchange_assoc,
        id_whiskerLeft, Iso.inv_hom_id, <-comp_whiskerRight_assoc,
      ]
      have hda : pw⟦hΓ.pwk_left_del⟧ ≫ da.den (C := C)
        = css⟦hΓ⟧ ≫ (!_ Γl.ety ▷ _) ≫ (λ_ _).hom ≫ da.den
        := by simp [Ctx?.SSplit.den_drop_left_assoc]
      rw [hda]
      apply refines_comp
      rfl
      apply refines_comp
      apply refines_whiskerRight
      apply σ.den_drop_pos el
      rfl
  | there hv hd =>
    have hΓr := da.del hd
    simp only [den, Ctx?.At.den, Category.assoc, ← tensor_comp_of_left_assoc, «at», Deriv.den_pwk,
      Ctx?.SSplit.den_pwk_right_del_assoc, <-rightUnitor_naturality]
    rw [<-tensorHom_def_of_right_assoc]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ
    apply M.drop_rem er (f := da.den) (hf := IsRem.of_del_le_pos (le_trans hd.del_le_quant hq))
    rfl

theorem SubstDS.den_at_neg
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hσ : σ.Neg e] {A} {q : Quant} (hv : Δ.At ⟨A, q⟩ n)
  : σ.den ≫ hv.den ↞ (σ.at hv).den (C := C) := by induction hσ generalizing n with
  | nil => cases hv
  | cons hΓ σ da hσ ha hl hr hcomm hq Iσ =>
  rename_i v a e el er Γ Γl Γr Δ
  cases hv with
  | here hd hv =>
    cases da with
    | zero => simp at hv
    | valid A' q da hq' =>
      have hΓl := σ.del;
      cases hv.ty
      simp only [«at», Deriv.cast_rfl, Deriv.den_pwk, den, Var?.ety, ety_var, Deriv?.den_valid,
        tensorHom_def, Ctx?.At.den, ge_iff_le, EQuant.one_le_coe, Var?.Wk.den_used, eqToHom_refl,
        PremonoidalCategory.whiskerLeft_id, Category.comp_id, Category.assoc, ← left_exchange_assoc,
        id_whiskerLeft, Iso.inv_hom_id, <-comp_whiskerRight_assoc,
      ]
      have hda : pw⟦hΓ.pwk_left_del⟧ ≫ da.den (C := C)
        = css⟦hΓ⟧ ≫ (!_ Γl.ety ▷ _) ≫ (λ_ _).hom ≫ da.den
        := by simp [Ctx?.SSplit.den_drop_left_assoc]
      rw [hda]
      apply refines_comp
      rfl
      apply refines_comp
      apply refines_whiskerRight
      apply σ.den_drop_neg el
      rfl
  | there hv hd =>
    have hΓr := da.del hd
    simp only [den, Ctx?.At.den, Category.assoc, ← tensor_comp_of_left_assoc, «at», Deriv.den_pwk,
      Ctx?.SSplit.den_pwk_right_del_assoc, <-rightUnitor_naturality]
    rw [<-tensorHom_def_of_right_assoc]
    apply refines_comp
    rfl
    apply refines_comp
    apply refines_tensorHom
    apply Iσ
    apply M.drop_add er (f := da.den) (hf := IsAdd.of_del_le_neg (le_trans hd.del_le_quant hq))
    rfl

theorem SubstSSplit.den_split_comm_eff (e : ε) {Γ Δ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ)
  [hσ : σ.CommEff e] {Δl Δr : Ctx? α} (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).den (C := C) = (σ.ssplit hΔ).den' (C := C)
  := by induction hσ generalizing Δl Δr with
  | nil =>
    cases hΔ; simp [SubstDS.ssplit, den_eq_ltimes, den', SubstDS.den, erase_left, left_exchange]
  | cons hΓ σ da hσ ha hl hr hcomm Iσ =>
    rename_i v a e el er Γ Γl Γr Δ
    simp only [den, den'] at Iσ
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
      simp only [SubstDS.ssplit, den_eq_ltimes, den']
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
      stop
      simp only [SubstDS.ssplit, Ctx?.den, Ctx?.ety, Ty.den, den_left, SubstDS.den,
        Deriv?.den_zero', tensorHom_def, comp_whiskerRight,
        PremonoidalCategory.whiskerLeft_comp, id_whiskerLeft, Category.assoc,
        den_right, <-left_exchange_assoc]
      congr 1
      rw [<-swap_whiskerLeft_of_swap_assoc, right_exchange_assoc, right_exchange_assoc]
      congr 1
      rw [left_exchange_assoc, left_exchange]
      rw [whiskerRight_swap_of_swap_assoc]
      rw [swap_whiskerRight_of_swap]
      apply Iσ
      rw [E.eff_comm_exchange hcomm]
    | sboth =>
      stop
      simp only [SubstDS.ssplit]
      if hv : v.used then
        rw [dite_cond_eq_true (by simp [hv]), den_left, den_right]
        simp only [
          SubstDS.den, tensorHom_def, Category.assoc, PremonoidalCategory.whiskerLeft_comp_assoc,
          comp_whiskerRight_assoc, PremonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
          <-left_exchange_assoc, Ctx?.den, Ty.den, Ctx?.ety
        ]
        rw [right_exchange_assoc, right_exchange_assoc]
        congr 1
        congr 1
        rw [
          whiskerLeft_swap_of_swap_assoc, <-swap_whiskerLeft_of_swap_assoc,
          <-whiskerRight_swap_of_swap_assoc
        ]
        sorry
        sorry
        sorry
        sorry
      else
        sorry

-- TODO: semantic substitution!
