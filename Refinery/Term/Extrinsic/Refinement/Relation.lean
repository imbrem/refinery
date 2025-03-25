import Refinery.Term.Extrinsic.Refinement.Beta
import Refinery.Term.Extrinsic.Refinement.Rewrite

open HasQuant

open HasPQuant

open HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive DRWS.refStep (R : DRWS φ α) : DRWS φ α
  | equiv {Γ A} {a b : Term φ (Ty α)} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
    : EquivStep Γ A a b da db → refStep R Γ A a b da db
  | beta {Γ A} {a b : Term φ (Ty α)} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
    : Beta Γ A a b da db → refStep R Γ A a b da db
  | base {Γ A} {a b : Term φ (Ty α)} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
    : R Γ A a b da db → refStep R Γ A a b da db

def DRWS.refines (R : DRWS φ α) : DRWS φ α := R.refStep.uniform
