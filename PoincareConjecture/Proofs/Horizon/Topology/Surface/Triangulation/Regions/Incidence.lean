


import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.CircleSides









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]




theorem exists_exactly_two_incident_components_of_chartCircle_edge
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
    (hcircle : chartCircle q r ⊆ ⋃ j, (edge j).map '' Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {s : Set M} (hs : s ∈ 𝓝 ((edge i).map t)) :
    ∃ u ∈ s, ∃ v ∈ s,
      u ∉ (⋃ j, (edge j).map '' Icc (0 : ℝ) 1) ∧
      v ∉ (⋃ j, (edge j).map '' Icc (0 : ℝ) 1) ∧
      connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ u ≠
        connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ v ∧
      ∀ x : M,
        (edge i).map t ∈
            frontier (connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x) ↔
          connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x =
              connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ u ∨
            connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x =
              connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ v := by
  let K : Set M := ⋃ j, (edge j).map '' Icc (0 : ℝ) 1
  have havoid : ∀ j, j ≠ i → (edge i).map t ∉ (edge j).map '' Icc (0 : ℝ) 1 := by
    intro j hji hj
    have hpoint := hmeet j hji ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, hj⟩
    rcases hpoint with hzero | hone
    · exact ht.1.ne' (hinj ⟨ht.1.le, ht.2.le⟩ (by simp) hzero)
    · exact ht.2.ne (hinj ⟨ht.1.le, ht.2.le⟩ (by simp) hone)
  let other : Set M := ⋃ j : {j : I // j ≠ i}, (edge j).map '' Icc (0 : ℝ) 1
  have hother : IsCompact other := isCompact_iUnion (fun j =>
    isCompact_Icc.image_of_continuousOn (edge j).smooth.continuousOn)
  have htother : (edge i).map t ∉ other := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact havoid j j.2 hj
  have hlocal : ∀ z ∈ otherᶜ, z ∈ K ↔ z ∈ chartCircle q r := by
    intro z hz
    refine ⟨?_, fun h => hcircle h⟩
    intro hzK
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzK
    by_cases hji : j = i
    · exact hedge (hji ▸ hj)
    · exact (hz (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
  have htCircle : (edge i).map t ∈ chartCircle q r :=
    hedge ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have htK : (edge i).map t ∈ K := hcircle htCircle
  obtain ⟨W, U, V, hWopen, htW, hWs, _, _, hUpath, hVpath,
    _, hpartition, htclosure⟩ :=
    exists_two_sided_edge_family_neighborhood edge i p hinj hsource ht havoid hs
  have hW : W ∈ 𝓝 ((edge i).map t) := hWopen.mem_nhds htW
  have hUV : U ∪ V ⊆ W \ K := by rw [hpartition]
  have hUK : U ⊆ Kᶜ := fun _ h => (hUV (Or.inl h)).2
  have hVK : V ⊆ Kᶜ := fun _ h => (hUV (Or.inr h)).2
  obtain ⟨u, hu⟩ := hUpath.nonempty
  obtain ⟨v, hv⟩ := hVpath.nonempty
  have hcomponent (z : M) (hzW : z ∈ W) (hzK : z ∉ K) :
      connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ u ∨
        connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ v := by
    have hzUV : z ∈ U ∪ V := by rw [← hpartition]; exact ⟨hzW, hzK⟩
    rcases hzUV with hzU | hzV
    · exact Or.inl (connectedComponentIn_eq
        (hUpath.isConnected.2.subset_connectedComponentIn hu hUK hzU)).symm
    · exact Or.inr (connectedComponentIn_eq
        (hVpath.isConnected.2.subset_connectedComponentIn hv hVK hzV)).symm
  obtain ⟨x, hxW, y, hyW, hxK, hyK, _, _, hxy⟩ :=
    exists_distinct_components_near_chartCircle q hr htarget hcircle htCircle
      (hother.isClosed.isOpen_compl.mem_nhds htother) hlocal hW
  have hdistinct : connectedComponentIn Kᶜ u ≠ connectedComponentIn Kᶜ v := by
    intro heq
    have hx : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ u :=
      (hcomponent x hxW hxK).elim id (fun h => h.trans heq.symm)
    have hy : connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ u :=
      (hcomponent y hyW hyK).elim id (fun h => h.trans heq.symm)
    exact hxy (hx.trans hy.symm)
  refine ⟨u, hWs (hUV (Or.inl hu)).1, v, hWs (hUV (Or.inr hv)).1,
    hUK hu, hVK hv, hdistinct, ?_⟩
  intro x
  exact Poincare.Topology.mem_frontier_connectedComponentIn_iff_of_two_sided_neighborhood
    hW hpartition hUpath.isConnected.2 hVpath.isConnected.2 hu hv htK
    htclosure.1 htclosure.2

end PoincareConjecture.Topology.Surface
