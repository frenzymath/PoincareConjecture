import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.OppositeCoordinate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Graph.BendGraph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Graph.LocalGraphSides
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_local_graph_two_segments (hdim : Module.finrank ℝ E = 2)
    {q a b : E} (ha : a ≠ q) (hb : b ≠ q)
    (hinter : segment ℝ q a ∩ segment ℝ q b ⊆ {q}) :
    ∃ h : E ≃ₜ (ℝ × ℝ), ∃ g : ℝ → ℝ, Continuous g ∧
      ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ ∀ z ∈ U,
        z ∈ segment ℝ q a ∪ segment ℝ q b ↔ (h z).2 = g (h z).1 := by
  obtain ⟨e, heu, hev⟩ := exists_continuousLinearEquiv_fst_neg_pos hdim
    (not_sameRay_sub_of_segments_inter_subset_singleton ha hb hinter)
  let f := (ContinuousAffineEquiv.vaddConst ℝ q).symm.trans e.toContinuousAffineEquiv
  have hfq : f q = 0 := by change e (q - q) = 0; simp
  have himage (c : E) : f '' segment ℝ q c = segment ℝ 0 (f c) := by
    have hi := image_segment ℝ f.toAffineEquiv.toAffineMap q c
    change f '' segment ℝ q c = segment ℝ (f q) (f c) at hi
    simpa only [hfq] using hi
  have hmem (c z : E) : z ∈ segment ℝ q c ↔ f z ∈ segment ℝ 0 (f c) := by
    rw [← himage]
    constructor
    · exact mem_image_of_mem f
    · rintro ⟨w, hw, hew⟩
      exact f.injective hew ▸ hw
  obtain ⟨V, hV, h0V, hgraph⟩ := exists_open_two_segments_graph heu hev
  refine ⟨f.toHomeomorph, bendGraph (f a) (f b), continuous_bendGraph _ _,
    f ⁻¹' V, hV.preimage f.continuous, ?_, ?_⟩
  · change f q ∈ V
    rw [hfq]
    exact h0V
  · intro z hz
    change z ∈ segment ℝ q a ∪ segment ℝ q b ↔
      (f z).2 = bendGraph (f a) (f b) (f z).1
    rw [mem_union, hmem a z, hmem b z, ← mem_union]
    exact hgraph (f z) hz

theorem hasLocalTwoSides_of_locally_two_segments (hdim : Module.finrank ℝ E = 2)
    {C : Set E} (hloc : ∀ q ∈ C, ∃ a b : E, a ≠ q ∧ b ≠ q ∧
      segment ℝ q a ∩ segment ℝ q b ⊆ {q} ∧
      ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ ∀ z ∈ U,
        z ∈ C ↔ z ∈ segment ℝ q a ∪ segment ℝ q b) : HasLocalTwoSides C := by
  apply hasLocalTwoSides_of_local_graph
  intro q hq
  obtain ⟨a, b, ha, hb, hinter, U, hU, hqU, hUC⟩ := hloc q hq
  obtain ⟨e, g, hg, V, hV, hqV, hgraph⟩ :=
    exists_local_graph_two_segments hdim ha hb hinter
  refine ⟨e, g, hg, U ∩ V, hU.inter hV, ⟨hqU, hqV⟩, ?_⟩
  intro z hz
  exact (hUC z hz.1).trans (hgraph z hz.2)

end Poincare.Manifold.Schoenflies.Plane
