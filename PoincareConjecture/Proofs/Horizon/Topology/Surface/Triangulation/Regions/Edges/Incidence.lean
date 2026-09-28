


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Incidence
import Mathlib.Topology.LocallyConstant.Basic









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem exists_exactly_two_incident_components_along_chartCircle_edge
    {I : Type v} [Finite I] (edge : I → SmoothEdge M) (i : I) (p q : M)
    (hinj : InjOn (edge i).map (Icc (0 : ℝ) 1))
    (hsource : (edge i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (hmeet : ∀ j, j ≠ i →
      (edge i).map '' Icc (0 : ℝ) 1 ∩ (edge j).map '' Icc (0 : ℝ) 1 ⊆
        {(edge i).map 0, (edge i).map 1})
    {r : ℝ} (hr : 0 < r)
    (htarget : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) q q) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target)
    (hedge : (edge i).map '' Icc (0 : ℝ) 1 ⊆ chartCircle q r)
    (hcircle : chartCircle q r ⊆ ⋃ j, (edge j).map '' Icc (0 : ℝ) 1) :
    ∃ u v : M,
      u ∉ (⋃ j, (edge j).map '' Icc (0 : ℝ) 1) ∧
      v ∉ (⋃ j, (edge j).map '' Icc (0 : ℝ) 1) ∧
      connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ u ≠
        connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ v ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : M,
        (edge i).map t ∈
            frontier (connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x) ↔
          connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x =
              connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ u ∨
            connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x =
              connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ v := by
  let K : Set M := ⋃ j, (edge j).map '' Icc (0 : ℝ) 1
  let T := {t : ℝ // t ∈ Ioo (0 : ℝ) 1}
  let incident (t : T) : Set M :=
    {x | (edge i).map t ∈ frontier (connectedComponentIn Kᶜ x)}
  have hpoint (t : T) : ∃ u v : M,
      u ∉ K ∧ v ∉ K ∧ connectedComponentIn Kᶜ u ≠ connectedComponentIn Kᶜ v ∧
      ∀ x : M, (edge i).map t ∈ frontier (connectedComponentIn Kᶜ x) ↔
        connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ u ∨
          connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ v := by
    obtain ⟨u, _, v, _, hu, hv, hne, hiff⟩ :=
      exists_exactly_two_incident_components_of_chartCircle_edge edge i p q hinj hsource
        hmeet hr htarget hedge hcircle t.property (s := univ) Filter.univ_mem
    exact ⟨u, v, hu, hv, hne, hiff⟩
  have hcurve : Continuous (fun t : T => (edge i).map t) :=
    ((edge i).smooth.continuousOn.mono Ioo_subset_Icc_self).domRestrict
  have hlocal : IsLocallyConstant incident := by
    apply (IsLocallyConstant.iff_exists_open incident).mpr
    intro t
    obtain ⟨W, U, V, hWopen, htW, _, _, _, hUpath, hVpath, _, hpartition,
      htclosure⟩ := exists_two_sided_edge_family_neighborhood_of_endpoint_intersections
        edge i p hinj hsource hmeet t.property (s := univ) Filter.univ_mem
    obtain ⟨a, ha⟩ := hUpath.nonempty
    obtain ⟨b, hb⟩ := hVpath.nonempty
    have htK : (edge i).map t ∈ K :=
      mem_iUnion.mpr ⟨i, ⟨t, Ioo_subset_Icc_self t.property, rfl⟩⟩
    have htiff (x : M) : (edge i).map t ∈ frontier (connectedComponentIn Kᶜ x) ↔
        connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ a ∨
          connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ b :=
      Poincare.Topology.mem_frontier_connectedComponentIn_iff_of_two_sided_neighborhood
        (hWopen.mem_nhds htW) hpartition hUpath.isConnected.2 hVpath.isConnected.2
        ha hb htK htclosure.1 htclosure.2
    refine ⟨(fun t : T => (edge i).map t) ⁻¹' W,
      hWopen.preimage hcurve, htW, ?_⟩
    intro t' ht'W
    obtain ⟨u, v, _, _, huv, ht'iff⟩ := hpoint t'
    have hbound (x : M)
        (hx : (edge i).map t' ∈ frontier (connectedComponentIn Kᶜ x)) :
        connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ a ∨
          connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ b :=
      Poincare.Topology.connectedComponentIn_eq_or_eq_of_two_sided_neighborhood
        (hWopen.mem_nhds ht'W) hpartition hUpath.isConnected.2 hVpath.isConnected.2 ha hb hx
    have hu := hbound u ((ht'iff u).mpr (Or.inl rfl))
    have hv := hbound v ((ht'iff v).mpr (Or.inr rfl))
    have hpair : ({connectedComponentIn Kᶜ u, connectedComponentIn Kᶜ v} : Set (Set M)) =
        {connectedComponentIn Kᶜ a, connectedComponentIn Kᶜ b} := by
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact (huv (hu.trans hv.symm)).elim
      · rw [hu, hv]
      · rw [hu, hv, pair_comm]
      · exact (huv (hu.trans hv.symm)).elim
    ext x
    change ((edge i).map t' ∈ frontier (connectedComponentIn Kᶜ x)) ↔
      (edge i).map t ∈ frontier (connectedComponentIn Kᶜ x)
    rw [ht'iff x, htiff x]
    change connectedComponentIn Kᶜ x ∈
        ({connectedComponentIn Kᶜ u, connectedComponentIn Kᶜ v} : Set (Set M)) ↔
      connectedComponentIn Kᶜ x ∈
        ({connectedComponentIn Kᶜ a, connectedComponentIn Kᶜ b} : Set (Set M))
    rw [hpair]
  let : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_Ioo
  let t₀ : T := ⟨1 / 2, by norm_num⟩
  obtain ⟨u, v, hu, hv, hne, hiff⟩ := hpoint t₀
  refine ⟨u, v, hu, hv, hne, ?_⟩
  intro t ht x
  have heq := hlocal.apply_eq_of_preconnectedSpace (⟨t, ht⟩ : T) t₀
  exact (Set.ext_iff.mp heq x).trans (hiff x)

end PoincareConjecture.Topology.Surface
