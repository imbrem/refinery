import Refinery.Term.Extrinsic.Refinement.Uniform
import Refinery.Term.Extrinsic.Semantics.Minimal

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

-- theorem RWS.uniform.ref {R : RWS φ α} [V : R.Valid C] {Γ A a b} (h : uniform R Γ A a b)
--   (Da : Γ ⊢ a : A) (Db : Γ ⊢ b : A) : Da.den (C := C) ↠ Db.den := by induction h with
--   | base h => apply V.den_ref h
--   | refl => apply refines_of_eq; apply Deriv.coherence
--   | trans hab hbc I I' => have ⟨Db'⟩ := hbc.wt.left; exact refines_trans (I Da Db') (I' Db' Db)
--   | let₁ hΓ ra rb Ia Ib =>
--     have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
--     have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
--     convert_to (Dax.let₁ hΓ Dbx).den (C := C) ↠ (Day.let₁ hΓ Dby).den
--     apply Deriv.coherence
--     apply Deriv.coherence
--     simp only [Deriv.den]
--     sorry
--   | let₂ hΓ ra rb Ia Ib =>
--     have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
--     have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
--     convert_to (Dax.let₂ hΓ Dbx).den (C := C) ↠ (Day.let₂ hΓ Dby).den
--     apply Deriv.coherence
--     apply Deriv.coherence
--     simp only [Deriv.den]
--     sorry
--   | pair hΓ ra rb Ia Ib =>
--     have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
--     have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
--     convert_to (Dax.pair hΓ Dbx).den (C := C) ↠ (Day.pair hΓ Dby).den
--     apply Deriv.coherence
--     apply Deriv.coherence
--     simp only [Deriv.den]
--     sorry
--   | inl ra Ia => cases Da with | inl da => cases Db with | inl db => simp [Deriv.den, Ia da db]
--   | inr ra Ia => cases Da with | inr da => cases Db with | inr db => simp [Deriv.den, Ia da db]
--   | abort ra Ia =>
--     cases Da with | abort da => cases Db with | abort db => simp [Deriv.den, Ia da db]
--   | iter hΓ hc hd ra rb Ia Ib =>
--     have ⟨Dax⟩ := ra.wt.left; have ⟨Dbx⟩ := rb.wt.left;
--     have ⟨Day⟩ := ra.wt.right; have ⟨Dby⟩ := rb.wt.right;
--     convert_to (Dax.iter hΓ hc hd Dbx).den (C := C) = (Day.iter hΓ hc hd Dby).den
--     apply Deriv.coherence
--     apply Deriv.coherence
--     simp only [Deriv.den, Ia Dax Day, Ib Dbx Dby]
--   | pos_unif hcr hlm hc hd hei => sorry
--   | neg_unif => sorry
