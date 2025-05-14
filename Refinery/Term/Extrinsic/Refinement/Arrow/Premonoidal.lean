import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Structure
import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Binoidal
import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.AssocNat
import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Central
import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.Symmetric
import Refinery.Term.Extrinsic.Refinement.Arrow.Premonoidal.UnitorNat

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

open CategoryTheory

instance DRWS.Obj.instPremonoidalCategory : PremonoidalCategory R.Obj where
  tensorHom_def _ _ := DRWS.Arrow.tensorHom_eq_ltimes _ _
  whiskerLeft_id _ _ := DRWS.Obj.whiskerLeft_id _
  id_whiskerRight _ _ := DRWS.Obj.id_whiskerRight _
  whiskerLeft_comp _ _ _ _ _ _ := DRWS.Arrow.whiskerLeft_comp _ _
  comp_whiskerRight _ _ _ := DRWS.Arrow.comp_whiskerRight _ _
  associator_central := DRWS.Arrow.pure_central (DRWS.Obj.assoc _ _ _)
  leftUnitor_central := DRWS.Arrow.pure_central (DRWS.Obj.leftUnitor _)
  rightUnitor_central := DRWS.Arrow.pure_central (DRWS.Obj.rightUnitor _)
  associator_naturality _ _ _ := DRWS.Arrow.associator_naturality _ _ _
  leftUnitor_naturality _ := DRWS.Arrow.leftUnitor_naturality _
  rightUnitor_naturality _ := DRWS.Arrow.rightUnitor_naturality _
  pentagon _ _ _ _ := sorry
  triangle _ _ := DRWS.Obj.triangle
