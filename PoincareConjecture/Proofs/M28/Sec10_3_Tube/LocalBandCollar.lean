import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalPartitionSides
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.ContainedCollar









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem transfer_graph_lower_collar_m28 (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    {s : ℝ} (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hgraph : range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
      range (fun q => A.coordinate_map (q, f q)))
    (hside : ∀ x ∈ A.carrier ∩ B.carrier,
      s < (B.coordinate_inverse x).2 ↔
        f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2)
    (K : Set M) (r : ℝ) (hr : 0 < r)
    (hcollar : ∀ x ∈ A.carrier,
      f (A.coordinate_inverse x).1 - r < (A.coordinate_inverse x).2 →
      (A.coordinate_inverse x).2 ≤ f (A.coordinate_inverse x).1 → x ∈ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ B.carrier,
      s - δ < (B.coordinate_inverse x).2 →
      (B.coordinate_inverse x).2 ≤ s → x ∈ K := by
  let V := A.aboveGraph_m28 (fun q => f q - r)
  have hV : IsOpen V := A.isOpen_aboveGraph_m28 _ (hf.sub continuous_const)
  have hc (q : UnitTwoSphere) : B.coordinate_map (q, s) ∈ V := by
    have hx : B.coordinate_map (q, s) ∈ range
        (fun q => A.coordinate_map (q, f q)) := hgraph ▸ mem_range_self q
    have hx' := (A.mem_coordinate_graph_iff_m28 f hdom).mp hx
    exact ⟨hx'.1, by rw [hx'.2]; exact sub_lt_self _ hr⟩
  obtain ⟨δ, hδ, hδV⟩ := B.exists_slice_collar_in_open hs V hV hc
  refine ⟨δ, hδ, ?_⟩
  intro x hx hlow hupp
  have habs : |(B.coordinate_inverse x).2 - s| < δ := abs_lt.mpr (by
    constructor <;> linarith)
  have hxV : x ∈ V := by
    have h := (hδV (B.coordinate_inverse x).1
      ((B.coordinate_inverse x).2 - s) habs).2
    have heq : s + ((B.coordinate_inverse x).2 - s) = (B.coordinate_inverse x).2 := by ring
    rw [heq, Prod.mk.eta, B.coordinate_map_coordinate_inverse hx] at h
    exact h
  apply hcollar x hxV.1 hxV.2
  exact le_of_not_gt (fun h => hupp.not_gt ((hside x ⟨hxV.1, hx⟩).mpr h))

end PoincareConjecture.EpsilonNeck
