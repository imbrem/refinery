import Refinery.Term.Extrinsic.Refinement.Semantics.Valid
import Refinery.Term.Extrinsic.Refinement.Rewrite

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

-- instance RWS.instLetMoveBivalid : BiValid (LetMove (S := S)) C where
--   den_eq h Dl Dr := by cases h with
--   | let_op hΓ hf da db =>
--     stop
--     rename_i Γ Γr Γl f a A B b
--     have hDl : Dl.den (C := C) = ((da.op hf).let₁ hΓ db).den := by apply Deriv.coherence
--     have hDr : Dr.den (C := C) = (da.let₁ hΓ
--                       (.let₁ (Γl.erase_right.cons (.right _))
--                         (.op hf (.bv (.here inferInstance (by simp)))) (db.wk1 _))).den
--             := by apply Deriv.coherence
--     rw [hDl, hDr]
--     simp only [
--       Deriv.den, Ctx?.SSplit.den, Var?.SSplit.den, Var?.erase, Var?.ety, ety_var,
--       swap_inner_tensorUnit_right, Ty.den, PremonoidalCategory.whiskerLeft_comp, Category.assoc,
--       Deriv.den_wk1, Ctx?.den, Ctx?.ety, Ctx?.At.den, Var?.Wk.den, eqToHom_refl,
--       tensorHom_def, PremonoidalCategory.whiskerLeft_id, Category.id_comp, M.drop_unit
--     ]
--     congr 2
--     simp only [<-Category.assoc]
--     congr 1
--     convert_to t⟦Γl.ety⟧ ◁ hf.den (C := C) =
--       (css⟦Γl.erase_right⟧ ≫ t⟦Γl.ety⟧ ◁ !_ Γl.erase.ety ≫ (ρ_ _).hom) ▷ t⟦A⟧
--         ≫ t⟦Γl.ety⟧ ◁ hf.den
--       using 1
--     premonoidal
--     rw [Ctx?.SSplit.den_drop_right_assoc, Ctx?.PWk.den_refl']
--     simp
--   | let_let₁ hΓ hΓc da db dc =>
--     stop
--     rename_i Γ Y Γr Γl Γc Γm a A b B c
--     have hDl : Dl.den (C := C) = ((da.let₁ hΓc db).let₁ hΓ dc).den := by apply Deriv.coherence
--     have hDr : Dr.den (C := C)
--       = (da.let₁ (hΓ.s1_23_12_3 hΓc) (db.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (dc.wk1 _))).den
--       := by apply Deriv.coherence
--     rw [hDl, hDr]
--     simp only [
--       Deriv.den, Deriv.den_wk1, PremonoidalCategory.whiskerLeft_comp, Category.assoc, Var?.erase,
--       Var?.ety, ety_var, Ctx?.den, Ctx?.ety, Ty.den, M.drop_unit, Ctx?.SSplit.den,
--       Var?.SSplit.den, tensorHom_def, swap_inner_tensorUnit_right,
--     ]
--     rw [<-Central.left_exchange_assoc]
--     rw [<-(hΓ.s1_23_12_3 hΓc).assoc_coherence_assoc (hΓ.s1_23_12 hΓc)]
--     premonoidal
--   | _ => sorry
