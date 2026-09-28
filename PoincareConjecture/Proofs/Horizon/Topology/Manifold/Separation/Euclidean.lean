import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Components
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Bounded
import Mathlib.Analysis.Convex.Contractible













open Set Topology

namespace Poincare.Topology



theorem collared_sphere_separates
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (e : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
      Set.Ioo (-1 : ℝ) 1) ≃ₜ U) :
    let S := Set.range (fun y =>
      (e (y, ⟨0, by norm_num⟩) : EuclideanSpace ℝ (Fin 3)))
    ∃ A B : Set (EuclideanSpace ℝ (Fin 3)),
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Sᶜ ∧ frontier A = S ∧ frontier B = S ∧
      (fun z => (e z : EuclideanSpace ℝ (Fin 3))) ''
        {z | (z.2 : ℝ) < 0} ⊆ A ∧
      (fun z => (e z : EuclideanSpace ℝ (Fin 3))) ''
        {z | 0 < (z.2 : ℝ)} ⊆ B ∧
      ((Bornology.IsBounded A ∧ ¬Bornology.IsBounded B) ∨
        (Bornology.IsBounded B ∧ ¬Bornology.IsBounded A)) := by
  let : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  obtain ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hAf, hBf, hL, hR⟩ :=
    exists_collar_complementary_regions (by norm_num : (0 : ℝ) < 1) hU e
  refine ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hAf, hBf, hL, hR, ?_⟩
  apply bounded_side_of_compact_complement_partition_euclidean_three
    (hA := hA) (hB := hB) (hdisj := hdis) (hcover := hcover)
  exact isCompact_range
    (continuous_subtype_val.comp (e.continuous.comp
      (continuous_id.prodMk continuous_const)))

end Poincare.Topology
