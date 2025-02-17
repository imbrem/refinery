import Refinery.Model
import Refinery.Ctx.Basic

import Discretion.Utils.Category

namespace Refinery

open CategoryTheory

open MonoidalCategory

open Monoidal

section TyModel

variable {α : Type _} [HasQuant α]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
         [TyModel α C]

notation "v⟦" v "⟧" => t⟦ Var?.ety v ⟧

abbrev Ctx?.den (Γ : Ctx? α ε) : C := t⟦Γ.ety⟧

notation "g⟦" Γ "⟧" => Ctx?.den Γ

end TyModel

section VarModel

variable {φ : Type _} {α : Type _} {ε : Type _} [Signature φ α ε]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [ChosenFiniteCoproducts C]
         [VarModel α C]


abbrev Var?.del.den {v : Var? α ε} (h : v.del) : (v⟦ v ⟧ : C) ⟶ 𝟙_ C
  := !_ v.ety

abbrev Var?.copy.den {v : Var? α ε} (h : v.copy) : (v⟦ v ⟧ : C) ⟶ v⟦ v ⟧ ⊗ v⟦ v ⟧
  := Δ_ v.ety

def Var?.Wk.den {v w : Var? α ε} (h : v ≤ w) : (v⟦ v ⟧ : C) ⟶ v⟦ w ⟧
  := match v, w, h with
  | v, ⟨B, 0, _⟩, h => (h.unused_del rfl).den
  | ⟨A, (_ : Quant), _⟩, ⟨B, (_ : Quant), _⟩, h => eq_hom (by cases h.ty; rfl)

def Ctx?.PWk.den {Γ Δ : Ctx? α ε} (h : Γ.PWk Δ) : (g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧
  := match Γ, Δ, h with
  | .nil, .nil, _ => 𝟙 (𝟙_ C)
  | .cons _ _, .cons _ _, h => h.tail.den ⊗ (Var?.Wk.den h.head)

def Var?.PSSplit.den {u v w : Var? α ε} : u.PSSplit v w → ((v⟦ u ⟧ : C) ⟶ v⟦ v ⟧ ⊗ v⟦ w ⟧)
  | .left _ _ _ => (ρ_ _).inv
  | .right _ _ _ => (λ_ _).inv
  | .sboth h => have _ := h.copy; Δ_ _

variable [BraidedCategoryStruct C]

def Ctx?.PSSplit.den {Γ Δ Ξ : Ctx? α ε} : Γ.PSSplit Δ Ξ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧ ⊗ g⟦ Ξ ⟧)
  | .nil => (λ_ _).inv
  | .cons hΓ hv => (hΓ.den ⊗ hv.den) ≫ swap_inner _ _ _ _

def Ctx?.Wk.den {Γ Δ : Ctx? α ε} : Γ.Wk Δ → ((g⟦ Γ ⟧ : C) ⟶ g⟦ Δ ⟧)
  | .nil => 𝟙 (𝟙_ C)
  | .cons hΓ hv => hΓ.den ⊗ (Var?.Wk.den hv)
  | .skip hΓ hv => (hΓ.den ⊗ hv.den) ≫ (ρ_ _).hom

def Var.Ix.den {Γ : Ctx? α ε} {v : Var? α ε} (h : v.Ix Γ) : (g⟦ Γ ⟧ : C) ⟶ v⟦ v ⟧
  := Ctx?.Wk.den h ≫ (λ_ _).hom

def Ctx?.At.den {v : Var? α ε} {Γ : Ctx? α ε} {n} (h : Γ.At v n) : (g⟦ Γ ⟧ : C) ⟶ v⟦ v ⟧ :=
  h.inductionOn
    (λ _ d _ h => (d.den ⊗ (Var?.Wk.den h)) ≫ (λ_ _).hom)
    (λ _ _ _ _ hw p => (p ⊗ hw.den) ≫ (ρ_ _).hom)

-- TODO: Ctx?.At.ix.den = Ctx?.At.den

-- TODO: Var?.Ix.at.den = Var?.Ix.den

-- TODO: PWk composition

-- TODO: den(PWk.toWk) = den(PWk)

-- TODO: PSSplit ; swap

-- TODO: PSSplit ==> PSSplit, PSSplit vs PSSplit?

-- TODO: Split? SSplit?

end VarModel
