import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.NeckGeometry.SourceNeckCoreBuffer
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CapGeometry.SourceCapBoundaryContact
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CapGeometry.SourceCapBoundaryGraphHit
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.InnerAttachment

/-!
# Actual off-path cap exclusion on the selected tube

Claim 10.4, pp. 250-251. A closed-core contact on the fixed tube produces
a boundary contact there. Actual first-exit buffers capture that contact,
and the original minimum crosses the resulting literal boundary graph.
The whole-path cap barrier gives the contradiction. See derivation 57.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

/-- The actual fixed source tube misses every canonical cap's closed core.
All frontier buffers, graph coordinates and path hits are produced from
the original source data, with accuracy before C and the flow. -/
theorem exists_source_tube_cap_exclusion_accuracy (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ (T : SourceTubeData S) (K : CapCertificate (E.flow.metric E.time)),
          K.epsilon = epsilon → K.cap_constant ≤ C →
          Disjoint K.closed_core (T.carrierOpen : Set _) := by
  obtain ⟨epsilonC, hCpos, _, hcontact⟩ := exists_source_cap_boundary_contact_accuracy.{u}
  obtain ⟨epsilonB, hBpos, hBsmall, hbuffer⟩ := exists_source_neck_core_buffer_accuracy P
  obtain ⟨epsilonG, hGpos, _, hhit⟩ := exists_cap_boundary_minimizer_hit_accuracy.{u}
  let epsilon₀ := min epsilonC (min epsilonB epsilonG)
  refine ⟨epsilon₀, lt_min hCpos (lt_min hBpos hGpos),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hBsmall, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall T K hepsilon hKC
  have hεC : epsilon ≤ epsilonC := hsmall.trans (min_le_left _ _)
  have hεB : epsilon ≤ epsilonB :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεG : epsilon ≤ epsilonG :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  apply disjoint_left.mpr
  intro x hxK hxT
  obtain ⟨⟨z, hzT, hzK⟩, havoid⟩ := hcontact E S hQ hεC T K hepsilon hKC x hxT hxK
  obtain ⟨N, hN, hzN⟩ := T.carrier_subset_neckCarrierUnion hzT
  obtain ⟨W, t, ht, hWε, hcenter, hWU, hzero, hone, hzW, haxis⟩ :=
    hbuffer E S hQ hεB N hN z hzN
  obtain ⟨v, hv, hvK⟩ := hhit (E.flow.slice E.time).carrier
    (E.flow.metric E.time) (E.flow.connection E.time) K W
    (by rw [hepsilon]; exact hεG) (by rw [hWε]; exact hεG)
    S.source_region.carrier hWU ht.1 ht.2 S.path_smooth S.source_region.path_mem
    S.source_region.minimizing hcenter hzero hone z hzK hzW haxis
  exact disjoint_left.mp havoid (K.boundary_subset_closed_core_m28 hvK)
    (mem_image_of_mem S.path ⟨hv.1.le, hv.2.le⟩)

end PoincareMT.M28
