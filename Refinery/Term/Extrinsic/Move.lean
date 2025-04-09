import Refinery.Term.Extrinsic.Effect

open HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive Move : Term φ (Ty α) → Term φ (Ty α) → Prop
  | let₁_let₁ {A B : Ty α} {a b c : Term φ (Ty α)}
    : Move (let₁ (let₁ a A b) B c) (let₁ a A (let₁ b B (↑¹ c)))
  | let₁_let₂ {A B C : Ty α} {a b c : Term φ (Ty α)}
    : Move (let₁ (let₂ a A B b) C c) (let₂ a A B (let₁ b C (↑¹ (↑¹ c))))
  | let₂_let₁ {A B C : Ty α} {a b c : Term φ (Ty α)}
    : Move (let₂ (let₁ a A b) B C c) (let₁ a A (let₂ b B C (↑² c)))
  | let₂_let₂ {A B C D : Ty α} {a b c d : Term φ (Ty α)}
    : Move (let₂ (let₂ a A B b) C D c) (let₂ a A B (let₂ b C D (↑² (↑² c))))
  | let₂_beta {A B : Ty α} {a b c : Term φ (Ty α)}
    : Move (let₂ (pair a b) A B c) (let₁ a A (let₁ (↑⁰ b) B c))
  | pair_let₁_left {A : Ty α} {a b c : Term φ (Ty α)}
    : Move (pair (let₁ a A b) c) (let₁ a A (pair b (↑⁰ c)))
  | pair_let₁_right {A : Ty α} {a b c : Term φ (Ty α)}
    (e : ε) (ha : HasEff e a) (he : e ⇌ ⊤)
    : Move (pair a (let₁ b A c)) (let₁ b A (pair (↑⁰ a) c))
  | pair_let₂_left {A B : Ty α} {a b c : Term φ (Ty α)}
    : Move (pair (let₂ a A B b) c) (let₂ a A B (pair b (↑⁰ (↑⁰ c))))
  | pair_let₂_right {A B : Ty α} {a b c : Term φ (Ty α)}
    (e : ε) (ha : HasEff e a) (he : e ⇌ ⊤)
    : Move (pair a (let₂ b A B c)) (let₂ b A B (pair (↑⁰ (↑⁰ a)) c))
  -- .. other moves...
