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
    : EquivStep.rel da db → refStep R Γ A a b da db
  | beta {Γ A} {a b : Term φ (Ty α)} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
    : Beta.rel da db → refStep R Γ A a b da db
  | base {Γ A} {a b : Term φ (Ty α)} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
    : R.rel da db → refStep R Γ A a b da db

def DRWS.refines (R : DRWS φ α) : DRWS φ α := R.refStep.uniform

instance DRWS.refines_coherent (R : DRWS φ α) : Coherent (R.refines) := R.refStep.uniform_coherent

inductive RWS.refStep (R : RWS φ α) : RWS φ α
  | equiv {Γ A} {a b : Term φ (Ty α)} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
    : DRWS.EquivStep.rel da db → refStep R Γ A a b
  | beta {Γ A} {a b : Term φ (Ty α)} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
    : DRWS.Beta.rel da db → refStep R Γ A a b
  | base {Γ A} {a b : Term φ (Ty α)}
    : R Γ A a b → refStep R Γ A a b

def RWS.refines (R : RWS φ α) : RWS φ α := R.refStep.uniform
