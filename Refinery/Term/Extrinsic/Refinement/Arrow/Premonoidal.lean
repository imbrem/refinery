import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Structure
import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Binoidal

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

open CategoryTheory

instance DRWS.Obj.instPremonoidalCategory : PremonoidalCategory R.Obj where
  tensorHom_def := sorry
  whiskerLeft_id _ _ := DRWS.Obj.whiskerLeft_id _
  id_whiskerRight _ _ := DRWS.Obj.id_whiskerRight _
  whiskerLeft_comp _ _ _ _ _ _ := DRWS.Arrow.whiskerLeft_comp _ _
  comp_whiskerRight _ _ _ := DRWS.Arrow.comp_whiskerRight _ _
  associator_central := sorry
  leftUnitor_central := sorry
  rightUnitor_central := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry
