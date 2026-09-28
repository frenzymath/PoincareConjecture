import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapEdgeFans
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.VertexFrontier








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)



theorem union_eventuallyEq_cap_at_open_chord (i : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (⋃ j, (B.face j).carrier) =ᶠ[𝓝 (((B.face i).boundary 0).map t)] (B.face i).carrier := by
  classical
  have havoid : ∀ᶠ z in 𝓝 (((B.face i).boundary 0).map t),
      ∀ j, j ≠ i → z ∉ (B.face j).carrier := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases he : j = i
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn he))
    · have hn := (B.open_chord_mem_carrier_iff i j ht).not.mpr he
      filter_upwards [(B.face j).isClosed_carrier.isOpen_compl.mem_nhds hn] with z hz
      exact fun _ => hz
  filter_upwards [havoid] with z hz
  apply propext
  constructor
  · intro hu
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases he : j = i
    · exact he ▸ hj
    · exact False.elim (hz j he hj)
  · exact fun hi => mem_iUnion.mpr ⟨i, hi⟩



theorem open_chord_mem_frontier_union (i : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (((B.face i).boundary 0).map t) ∈ frontier (⋃ j, (B.face j).carrier) := by
  have hcap := (B.face i).boundary_image_subset_frontier 0 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  refine ⟨subset_closure (mem_iUnion.mpr
    ⟨i, (B.open_chord_mem_carrier_iff i i ht).mpr rfl⟩), ?_⟩
  intro hint
  apply hcap.2
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [mem_interior_iff_mem_nhds.mp hint,
    B.union_eventuallyEq_cap_at_open_chord i ht] with z hz he
  exact (propext_iff.mp he).mp hz


theorem chord_subset_frontier_union (i : Bool × Bool) :
    (((B.face i).boundary 0).map '' Icc (0 : ℝ) 1) ⊆
      frontier (⋃ j, (B.face j).carrier) := by
  have hmap : MapsTo (((B.face i).boundary 0).map) (Ioo (0 : ℝ) 1)
      (frontier (⋃ j, (B.face j).carrier)) :=
    fun _ ht => B.open_chord_mem_frontier_union i ht
  have hc : ContinuousOn (((B.face i).boundary 0).map) (closure (Ioo (0 : ℝ) 1)) := by
    rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
    exact ((B.face i).boundary 0).smooth.continuousOn
  have h := hmap.closure_of_continuousOn hc
  rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1), isClosed_frontier.closure_eq] at h
  exact h.image_subset



theorem frontier_union_eq_chords : frontier (⋃ i, (B.face i).carrier) =
    ⋃ i, (((B.face i).boundary 0).map '' Icc (0 : ℝ) 1) := by
  apply subset_antisymm B.frontier_union_subset_chords
  exact iUnion_subset fun i => B.chord_subset_frontier_union i

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
