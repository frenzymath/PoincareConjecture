import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Topology
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

variable {X : Type*} [TopologicalSpace X]

theorem isClosed_connectedComponentIn_of_isClosed {S : Set X}
    (hS : IsClosed S) (x : X) : IsClosed (connectedComponentIn S x) := by
  by_cases hx : x ∈ S
  · rw [connectedComponentIn_eq_image hx]
    exact hS.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

theorem frontier_superlevel_component_subset [LocallyConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (B : ℝ) (x : X) :
    frontier (connectedComponentIn {y | B ≤ f y} x) ⊆ {y | f y = B} := by
  have hclosed : IsClosed (connectedComponentIn {y | B ≤ f y} x) :=
    isClosed_connectedComponentIn_of_isClosed
    (isClosed_le continuous_const hf) x
  intro y hy
  have hyX : y ∈ connectedComponentIn {z | B ≤ f z} x := by
    simpa only [hclosed.closure_eq] using frontier_subset_closure hy
  have hscalar := connectedComponentIn_subset {z | B ≤ f z} x hyX
  apply le_antisymm ?_ hscalar
  by_contra h
  have hstrict : B < f y := lt_of_not_ge h
  let V := connectedComponentIn {z | B < f z} y
  have hV : IsOpen V := (isOpen_lt continuous_const hf).connectedComponentIn
  have hyV : y ∈ V := mem_connectedComponentIn hstrict
  have hsub : V ⊆ connectedComponentIn {z | B ≤ f z} x := by
    rw [connectedComponentIn_eq hyX]
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn hyV
    intro z hz
    exact le_of_lt (show B < f z from connectedComponentIn_subset {z | B < f z} y hz)
  exact hy.2 (mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hV.mem_nhds hyV) hsub))

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem exists_closed_scalar_region (e : TerminalEnd K)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D)) (B : ℝ) :
    ∃ n : ℕ, ∃ X : Set (E.extended.slice T).carrier,
      IsClosed X ∧ IsConnected X ∧ Subtype.val '' e.tail n ⊆ X ∧
      X ⊆ K.component ∧ (∀ x ∈ X, B ≤ (E.extended.connection T).scalarCurvature x) ∧
      frontier X ⊆ {x | (E.extended.connection T).scalarCurvature x = B} ∧
      IsCompact (frontier X) := by
  let : LocallyConnectedSpace (E.extended.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  let R := (E.extended.connection T).scalarCurvature
  have hR : Continuous R := (E.extended.connection T).continuous_scalarCurvature
  obtain ⟨n, hn⟩ := e.exists_tail_scalar_gt hlower hproper B
  obtain ⟨x, hx⟩ := (e.tail_image_connected n).nonempty
  have htail : Subtype.val '' e.tail n ⊆ {z | B ≤ R z} := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hn n le_rfl z hz).le
  let X := connectedComponentIn {z | B ≤ R z} x
  have hxS : x ∈ {z | B ≤ R z} := htail hx
  have hxX : x ∈ X := mem_connectedComponentIn hxS
  have hXclosed : IsClosed X := SingularRegularLimit.isClosed_connectedComponentIn_of_isClosed
    (isClosed_le continuous_const hR) x
  have hXconnected : IsConnected X := isConnected_connectedComponentIn_iff.mpr hxS
  have hxK : x ∈ K.component := by obtain ⟨y, _, rfl⟩ := hx; exact y.property
  have hcomponent : connectedComponent x = K.component := by
    rw [K.component_eq] at hxK ⊢
    exact (connectedComponent_eq hxK).symm
  have hXK : X ⊆ K.component := by
    rw [← hcomponent]
    exact hXconnected.subset_connectedComponent hxX
  have hfront : frontier X ⊆ {z | R z = B} :=
    SingularRegularLimit.frontier_superlevel_component_subset hR B x
  refine ⟨n, X, hXclosed, hXconnected,
    (e.tail_image_connected n).isPreconnected.subset_connectedComponentIn hx htail,
    hXK, fun z hz => connectedComponentIn_subset _ x hz, hfront, ?_⟩
  exact (hproper {B} isCompact_singleton).of_isClosed_subset isClosed_frontier hfront

end PoincareConjecture.TerminalEnd
