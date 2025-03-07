import Refinery.Term.Extrinsic.Minimal
import Refinery.Ctx.Semantics.Minimal
import Refinery.Term.Extrinsic.Semantics.Wk

namespace Refinery

open CategoryTheory

open MonoidalCategory' PremonoidalCategory DistributiveCategory

open scoped MonoidalCategory

open ChosenFiniteCoproducts

variable {φ : Type _} {α : outParam (Type _)} {ε : outParam (Type _)} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [BraidedCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

namespace Term

def SDeriv.den {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  : (Γ ⊢ₛ a : A) → ((g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧)
  | .bv hv => hv.den
  | .op hf da => da.den ≫ hf.den
  | .let₁ dΓ dq da db => dΓ.den ≫ (_ ◁ da.den) ≫ (_ ◁ dq.den) ≫ db.den
  | .unit dΓ => haveI _ := dΓ.del; !_ _
  | .pair dΓ da db => dΓ.den ≫ (da.den ⋉ db.den)
  | .let₂ dΓ dqa dqb da db => dΓ.den ≫ (_ ◁ da.den)
    ≫ (α_ _ _ _).inv
    ≫ (_ ◁ dqa.den) ▷ _
    ≫ _ ◁ dqb.den ≫ db.den
  | .inl da => da.den ≫ CC.inl _ _
  | .inr db => db.den ≫ CC.inr _ _
  | .case dΓ dΓl dqa dqb da db dc =>
    dΓ.den ≫ (_ ◁ da.den) ≫ (∂L _ _ _).inv
           ≫ desc ((dΓl.zwkLeft.den ⊗ dqa.den) ≫ db.den) ((dΓl.zwkRight.den ⊗ dqb.den) ≫ dc.den)
  | .abort da => da.den ≫ CC.fromZero _
  | .iter (A := A) (B := B) (Γl := Γl) dΓ dq _ _ da db =>
    dΓ.den ≫ (_ ◁ da.den) ≫ iterate (
      Δ_ Γl.ety ▷ _
        ≫ (α_ _ _ _).hom
        ≫ _ ◁ _ ◁ dq.den
        ≫ _ ◁ db.den
        ≫ (∂L g⟦Γl⟧ t⟦B⟧ t⟦A⟧).inv
        ≫ ((!_ Γl.ety ▷ _ ≫ (λ_ _).hom) ⊕ₕ 𝟙 _))

theorem SDeriv.den_cast {Γ Γ' : Ctx? α} {A A' : Ty α} {a a' : Term φ (Ty α)}
  (hΓ : Γ = Γ') (hA : A = A') (ha : a = a') (D : Γ ⊢ₛ a : A)
  : (D.cast hΓ hA ha).den (C := C) = eqToHom (by rw [hΓ]) ≫ D.den ≫ eqToHom (by rw [hA])
  := by cases hΓ; cases hA; cases ha; simp

theorem SDeriv.den_cast_term {Γ : Ctx? α} {A : Ty α} {a a' : Term φ (Ty α)}
  (ha : a = a') (D : Γ ⊢ₛ a : A)
  : (D.cast_term ha).den (C := C) = D.den
  := by cases ha; rfl

theorem Deriv.den_zwk {Γ Δ : Ctx? α} (ρ : Γ.ZWk Δ) {A : Ty α} {a : Term φ (Ty α)} (D : Δ ⊢ a : A)
  : (D.pwk ρ).den (C := C) = ρ.den ≫ D.den := by rw [<-ρ.den_toPWk, den_pwk]

theorem SDeriv.den_unstrict {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ a : A)
  : D.unstrict.den = D.den (C := C) := by
  induction D <;> simp [
    den, unstrict, Deriv.den, Deriv.den_pwk, Deriv.den_zwk, tensorHom_def, Ctx?.SAt.den_unstrict,
    Ctx?.ZWk.den_toPWk, <-Var?.ZWk.den_toWk, *]

def FDeriv.den {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ' a : A)
  : (g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧ := D.drop.den ≫ D.deriv.den

theorem FDeriv.den_toDeriv {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ₛ' a : A)
  : D.toDeriv.den (C := C) = D.den := by simp only [toDeriv, Deriv.den_pwk, Ctx?.ZWk.den_toPWk,
    SDeriv.den_unstrict, den]

--TODO: golf
theorem SDeriv.coherence {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (D D' : Γ ⊢ₛ a : A) : D.den (C := C) = D'.den := by induction D with
  | bv x => cases D' with | bv x' => rw [Subsingleton.elim x x']
  | op hf => cases D' with | op hf' =>
    cases hf.trg; cases hf'.trg; cases hf.src; cases hf'.src
    simp only [den]; congr 1; apply_assumption
  | let₁ σ ρ da db => cases D' with
    | let₁ σ' ρ' da' db' =>
      cases shunt_right_ctx_eq_ssplit σ σ' da da'
      cases shunt_left_one_eq_ssplit σ σ' ρ ρ' db db'
      simp only [den]
      congr 1
      apply Ctx?.SSplit.coherence
      congr 2
      apply_assumption
      congr 1
      apply Var?.ZWk.coherence
      apply_assumption
  | unit ρ => cases D' with | unit ρ' => rfl
  | pair σ da db => cases D' with | pair σ' da' db' =>
    cases shunt_left_ctx_eq_ssplit σ σ' da da'
    cases shunt_right_ctx_eq_ssplit σ σ' db db'
    simp only [den]
    congr 1
    apply Ctx?.SSplit.coherence
    congr 1 <;> apply_assumption
  | let₂ σ ρ₁ ρ₂ da db => cases D' with | let₂ σ' ρ₁' ρ₂' da' db' =>
    cases shunt_right_ctx_eq_ssplit σ σ' da da'
    cases shunt_left_two_eq_ssplit σ σ' ρ₁ ρ₂ ρ₁' ρ₂' db db'
    simp only [den]
    congr 1
    apply Ctx?.SSplit.coherence
    congr 2
    apply_assumption
    congr 2
    congr 1
    apply Var?.ZWk.coherence
    apply_assumption
    apply Var?.ZWk.coherence
    apply_assumption
  | inl da => cases D' with | inl da' => simp only [den]; congr 1; apply_assumption
  | inr db => cases D' with | inr db' => simp only [den]; congr 1; apply_assumption
  | case σ σm ρ₁ ρ₂ da db dc => cases D' with | case σ' σm' ρ₁' ρ₂' da' db' dc' =>
    cases shunt_right_ctx_eq_ssplit σ σ' da da'
    have h := db.eq_of_zqeq db' ?h
    cases h
    have h := dc.eq_of_zqeq dc' ?h'
    cases h
    cases σm.in_eq σm'
    simp only [den]
    congr 1
    apply Ctx?.SSplit.coherence
    congr 2
    apply_assumption
    congr 2
    congr 1
    apply Ctx?.ZWk.coherence
    apply Var?.ZWk.coherence
    apply_assumption
    congr 1
    apply Ctx?.ZWk.coherence
    apply Var?.ZWk.coherence
    apply_assumption
    constructor
    apply Ctx?.ZQEq.zig
    apply σ.zle_left.trans σm.zle_right
    apply σ'.zle_left.trans σm'.zle_right
    exact ρ₂.shunt_zqeq ρ₂'
    constructor
    apply Ctx?.ZQEq.zig
    apply σ.zle_left.trans σm.zle_left
    apply σ'.zle_left.trans σm'.zle_left
    exact ρ₁.shunt_zqeq ρ₁'
  | abort da => cases D' with | abort da' => simp only [den]; congr 1; apply_assumption
  | iter σ ρ hc hd da db => cases D' with | iter σ' ρ' hc' hd' da' db' =>
    cases shunt_right_ctx_eq_ssplit σ σ' da da'
    cases shunt_left_one_eq_ssplit σ σ' ρ ρ' db db'
    simp only [den]
    congr 1
    apply Ctx?.SSplit.coherence
    congr 2
    apply_assumption
    congr 5
    apply Var?.ZWk.coherence
    apply_assumption

theorem FDeriv.coherence {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  : (D D' : Γ ⊢ₛ' a : A) → D.den (C := C) = D'.den
  | ⟨Γ, ρ, D⟩, ⟨Γ', ρ', D'⟩ => by
    cases D.eq_of_zqeq D' (ρ.shunt_zqeq ρ')
    simp only [den]
    congr 1
    apply Ctx?.ZWk.coherence
    apply SDeriv.coherence

theorem Deriv.den_factor {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (D : Γ ⊢ a : A)
  : D.factor.den (C := C) = D.den := by induction D with
  | bv x => exact x.factor_den (C := C)
  | op | inl | inr | abort =>
    simp only [factor, den, FDeriv.den]; rw [SDeriv.den, <-Category.assoc]; congr
  | let₁ σ da db Ia Ib =>
    simp only [factor, den]
    split
    rename_i db' Γ v ρ hvw db'' heq
    simp only [FDeriv.den]
    rw [SDeriv.den, <-Ctx?.SSplit.den_fuse_assoc, tensorHom_def_of_left]
    simp only [Category.assoc]
    rw [Central.left_exchange_assoc (f := ρ.den), <-PremonoidalCategory.whiskerLeft_comp_assoc]
    congr
    rw [<-Ib, heq]
    simp [FDeriv.den, tensorHom_def]
  | unit =>
    simp [den, factor, FDeriv.den, SDeriv.den]
    rw [M.drop_aff ⊥ _ (h := _) (hA := _) (hB := _)]
    apply Ctx?.ZWk.den_pure
  | pair σ da db Ia Ib =>
    simp only [factor, den, FDeriv.den]
    rw [SDeriv.den, <-Ctx?.SSplit.den_fuse_assoc, tensorHom_def]
    simp only [Category.assoc, ltimes, <-Central.right_exchange_assoc]
    rw [<-PremonoidalCategory.comp_whiskerRight_assoc, <-PremonoidalCategory.whiskerLeft_comp]
    congr
  | let₂ σ da db Ia Ib =>
    simp only [factor, den]
    split
    rename_i db' Γ v ρ ρ' hvw db'' heq
    simp only [FDeriv.den]
    rw [SDeriv.den, <-Ctx?.SSplit.den_fuse_assoc, tensorHom_def_of_left]
    simp only [Category.assoc]
    rw [Central.left_exchange_assoc (f := ρ.den), <-PremonoidalCategory.whiskerLeft_comp_assoc]
    congr 2
    congr
    rw [<-Ib, heq]
    simp [FDeriv.den, tensorHom_def]
  | case σ da db dc Ia Ib Ic =>
    simp only [factor, den]
    split
    rename_i db' dc' Γb vb ρb ρb' db'' Γc vc ρc ρc' dc'' heqb heqc
    simp only [FDeriv.den]
    rw [SDeriv.den, <-Ctx?.SSplit.den_fuse_assoc, tensorHom_def_of_left]
    simp only [Category.assoc]
    congr 1
    rw [Central.left_exchange_assoc, <-PremonoidalCategory.whiskerLeft_comp_assoc]
    congr 1
    congr
    simp only [Ty.den]
    rw [DistributiveCategory.distl_inv_naturality_left_assoc]
    congr 1
    simp only [addHom, desc_comp, Category.assoc, inl_desc, inr_desc]
    congr
    rw [<-Ib, heqb]
    simp [FDeriv.den, tensorHom_def]
    rw [<-PremonoidalCategory.comp_whiskerRight_assoc, <-Ctx?.ZWk.den_comp]
    congr 2
    apply Ctx?.ZWk.coherence
    rw [<-Ic, heqc]
    simp [FDeriv.den, tensorHom_def]
    rw [<-PremonoidalCategory.comp_whiskerRight_assoc, <-Ctx?.ZWk.den_comp]
    congr 2
    apply Ctx?.ZWk.coherence
  | iter σ hc hd da db Ia Ib =>
    simp only [factor, den]
    split
    rename_i db' Γ v ρ hvw db'' heq
    simp only [FDeriv.den]
    rw [SDeriv.den, <-Ctx?.SSplit.den_fuse_assoc, tensorHom_def_of_left]
    simp only [Category.assoc]
    rw [Central.left_exchange_assoc (f := ρ.den), <-PremonoidalCategory.whiskerLeft_comp_assoc]
    congr
    apply E.pure_uniform
    have _ := ρ.copy
    rw [<-PremonoidalCategory.comp_whiskerRight_assoc, M.copy_rel_ltimes ⊥ ρ.den (hA := _)]
    simp only [comp_whiskerRight, whisker_assoc, Ty.den.eq_5, Category.assoc, Iso.inv_hom_id_assoc,
      desc_comp, inl_desc, Category.id_comp, inr_desc]
    congr 1
    rw [PremonoidalCategory.associator_naturality_left_assoc]
    congr 1
    simp only [Central.left_exchange_assoc]
    simp only [<-PremonoidalCategory.whiskerLeft_comp_assoc]
    congr 1
    congr
    rw [<-Ib, heq]
    simp [FDeriv.den, tensorHom_def]
    rw [DistributiveCategory.distl_inv_naturality_left_assoc]
    simp only [addHom, desc_comp, Category.assoc, inl_desc, inr_desc, Category.id_comp,
      Iso.cancel_iso_inv_left]
    congr 1
    rw [<-PremonoidalCategory.comp_whiskerRight_assoc, M.drop_aff ⊥]

theorem Deriv.coherence {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (D D' : Γ ⊢ a : A) : D.den (C := C) = D'.den
  := by rw [<-D.den_factor, <-D'.den_factor, D.factor.coherence D'.factor]
