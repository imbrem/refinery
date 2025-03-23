import Refinery.Term.Extrinsic.Refinement.Semantics.Valid
import Refinery.Term.Extrinsic.Refinement.Beta
import Refinery.Term.Extrinsic.Semantics.Subst

namespace Refinery

open CategoryTheory MonoidalCategory' PremonoidalCategory DistributiveCategory
     ChosenFiniteCoproducts

open scoped MonoidalCategory

open HasCommRel HasQuant

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [PremonoidalCategory C] [CC : ChosenFiniteCoproducts C]
        [SymmetricCategory' C] [Iterate C] [E : Elgot2 C ε] [M : Model φ α ε C]

theorem DRWS.Beta.Valid : Valid (Beta (S := S)) C where
  den_ref da db h := by cases h with
  | beta_pos hΓ da q hq db ha hb he heq =>
    simp only [Ctx?.den, Deriv.den, Deriv.den_pwk, Ctx?.ety, Var?.ety, ety_var, Ty.den.eq_3,
      Ctx?.PWk.den, Ctx?.PWk.den_refl, ge_iff_le, EQuant.one_le_coe, Var?.Wk.den_used, eqToHom_refl,
      tensorHom_id, id_whiskerRight, Category.id_comp]
    rw [<-Category.assoc]
    convert db.den_subst_pos he (.subst0 hΓ da q hq) using 2
    simp [SubstDS.subst0, SubstDS.den]
    constructor
    infer_instance
    constructor
    assumption
    apply bot_le
    rfl
    apply commutes_bot_left
    apply le_trans _ heq
    simp [quant]
  | beta_neg hΓ da q hq db ha hb he heq =>
    simp only [Ctx?.den, Deriv.den, Deriv.den_pwk, Ctx?.ety, Var?.ety, ety_var, Ty.den.eq_3,
      Ctx?.PWk.den, Ctx?.PWk.den_refl, ge_iff_le, EQuant.one_le_coe, Var?.Wk.den_used, eqToHom_refl,
      tensorHom_id, id_whiskerRight, Category.id_comp]
    rw [<-Category.assoc]
    convert db.den_subst_neg he (.subst0 hΓ da q hq) using 2
    simp [SubstDS.subst0, SubstDS.den]
    constructor
    infer_instance
    constructor
    assumption
    apply bot_le
    rfl
    apply commutes_bot_left
    apply le_trans _ heq
    simp [quant]
