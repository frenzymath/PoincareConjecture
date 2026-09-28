import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitEdges
import PoincareConjecture.Proofs.M76.Mathlib.PolygonChordCompatibility










set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} {m n : ℕ}



theorem injective_split (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (hinj : Function.Injective (Fin.append u v)) :
    Function.Injective (Fin.snoc u (v 0) : Fin ((m + 1) + 1) → E) ∧
      Function.Injective (Fin.snoc v (u 0) : Fin ((n + 1) + 1) → E) := by
  obtain ⟨hu, hv, hdis⟩ := Fin.append_injective_iff.mp hinj
  constructor
  · apply Fin.snoc_injective_of_injective hu
    rintro ⟨i, hi⟩
    exact hdis i 0 hi
  · apply Fin.snoc_injective_of_injective hv
    rintro ⟨i, hi⟩
    exact hdis 0 i hi.symm



theorem edgeVertices_split_left_cases (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin ((m + 1) + 1)) :
    (∃ j, ((mk (Fin.snoc u (v 0))).edgeVertices i : Set E) =
      ((mk (Fin.append u v)).edgeVertices j : Set E)) ∨
        ((mk (Fin.snoc u (v 0))).edgeVertices i : Set E) = {u 0, v 0} := by
  induction i using Fin.lastCases with
  | last =>
    right
    rw [edgeVertices_snoc_last, pair_comm]
  | cast i =>
    left
    exact ⟨i.castAdd (n + 1), congrArg (fun s : Finset E => (s : Set E))
      (edgeVertices_split_left u v i)⟩



theorem edgeVertices_split_right_cases (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin ((n + 1) + 1)) :
    (∃ j, ((mk (Fin.snoc v (u 0))).edgeVertices i : Set E) =
      ((mk (Fin.append u v)).edgeVertices j : Set E)) ∨
        ((mk (Fin.snoc v (u 0))).edgeVertices i : Set E) = {u 0, v 0} := by
  induction i using Fin.lastCases with
  | last => exact Or.inr (edgeVertices_snoc_last v (u 0))
  | cast i =>
    left
    exact ⟨Fin.natAdd (m + 1) i, congrArg (fun s : Finset E => (s : Set E))
      (edgeVertices_split_right u v i)⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem hasSimplicialEdges_split (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (hP : (mk (Fin.append u v)).HasSimplicialEdges)
    (hinj : Function.Injective (Fin.append u v))
    (hchord : segment ℝ (u 0) (v 0) ∩ (mk (Fin.append u v)).boundary ℝ ⊆ {u 0, v 0}) :
    (mk (Fin.snoc u (v 0))).HasSimplicialEdges ∧
      (mk (Fin.snoc v (u 0))).HasSimplicialEdges := by
  have hd : segment ℝ ((mk (Fin.append u v)) ((0 : Fin (m + 1)).castAdd (n + 1)))
      ((mk (Fin.append u v)) (Fin.natAdd (m + 1) (0 : Fin (n + 1)))) ∩
        (mk (Fin.append u v)).boundary ℝ ⊆
      {(mk (Fin.append u v)) ((0 : Fin (m + 1)).castAdd (n + 1)),
        (mk (Fin.append u v)) (Fin.natAdd (m + 1) (0 : Fin (n + 1)))} := by
    simpa only [Fin.append_left, Fin.append_right] using hchord
  constructor
  · apply (mk (Fin.append u v)).hasSimplicialEdges_of_edges_or_chord hP hinj _ _ hd
    intro i
    simpa only [Fin.append_left, Fin.append_right] using edgeVertices_split_left_cases u v i
  · apply (mk (Fin.append u v)).hasSimplicialEdges_of_edges_or_chord hP hinj _ _ hd
    intro i
    simpa only [Fin.append_left, Fin.append_right] using edgeVertices_split_right_cases u v i

end Polygon
