import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutComponents
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts.Resolution



noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private instance : ConnectedSpace S1 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

private theorem card_index_eq_connectedComponents_of_circle_family
    {ι : Type*} [Finite ι] (f : ι → S1 → S2) (hf : ∀ i, Continuous (f i))
    (hinj : Injective (fun z : ι × S1 => f z.1 z.2))
    {L : Set S2} (hcover : (⋃ i, range (f i)) = L) :
    Nat.card ι = Nat.card (ConnectedComponents L) := by
  have hdisjoint : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨p, hp⟩ ⟨q, hq⟩
    exact hij (congrArg Prod.fst
      (hinj (a₁ := (i, p)) (a₂ := (j, q)) (hp.trans hq.symm)))
  exact (Poincare.Topology.card_connectedComponents_of_finite_closed_cover
    (fun i => range (f i)) (fun i => (isCompact_range (hf i)).isClosed)
    (fun i => isConnected_range (hf i)) hdisjoint hcover).symm

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}



theorem card_lowerCutIndex_eq_card_connectedComponents
    (A : AnnularEndFamily v g B C) :
    Nat.card A.LowerCutIndex =
      Nat.card (ConnectedComponents {p : S2 | inner Real v (g p) = A.lowerCut}) :=
  card_index_eq_connectedComponents_of_circle_family A.lowerCutCircle
    (fun i => (A.lowerCutCircle_geometry i).1.continuous)
    A.lowerCutCircle_joint_injective A.iUnion_range_lowerCutCircle



theorem card_upperCutIndex_eq_card_connectedComponents
    (A : AnnularEndFamily v g B C) :
    Nat.card A.UpperCutIndex =
      Nat.card (ConnectedComponents {p : S2 | inner Real v (g p) = A.upperCut}) :=
  card_index_eq_connectedComponents_of_circle_family A.upperCutCircle
    (fun i => (A.upperCutCircle_geometry i).1.continuous)
    A.upperCutCircle_joint_injective A.iUnion_range_upperCutCircle

theorem card_lowerCutIndex_eq_one_of_isConnected
    (A : AnnularEndFamily v g B C)
    (hconn : IsConnected {p : S2 | inner Real v (g p) = A.lowerCut}) :
    Nat.card A.LowerCutIndex = 1 := by
  let : ConnectedSpace {p : S2 | inner Real v (g p) = A.lowerCut} :=
    isConnected_iff_connectedSpace.mp hconn
  rw [A.card_lowerCutIndex_eq_card_connectedComponents]
  exact Nat.card_unique

theorem card_upperCutIndex_eq_one_of_isConnected
    (A : AnnularEndFamily v g B C)
    (hconn : IsConnected {p : S2 | inner Real v (g p) = A.upperCut}) :
    Nat.card A.UpperCutIndex = 1 := by
  let : ConnectedSpace {p : S2 | inner Real v (g p) = A.upperCut} :=
    isConnected_iff_connectedSpace.mp hconn
  rw [A.card_upperCutIndex_eq_card_connectedComponents]
  exact Nat.card_unique

theorem card_lowerCutIndex_eq_two_of_card_connectedComponents
    (A : AnnularEndFamily v g B C)
    (hcard : Nat.card
      (ConnectedComponents {p : S2 | inner Real v (g p) = A.lowerCut}) = 2) :
    Nat.card A.LowerCutIndex = 2 :=
  A.card_lowerCutIndex_eq_card_connectedComponents.trans hcard

theorem card_upperCutIndex_eq_two_of_card_connectedComponents
    (A : AnnularEndFamily v g B C)
    (hcard : Nat.card
      (ConnectedComponents {p : S2 | inner Real v (g p) = A.upperCut}) = 2) :
    Nat.card A.UpperCutIndex = 2 :=
  A.card_upperCutIndex_eq_card_connectedComponents.trans hcard

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily
