import PoincareLib.Topology.Manifold.Surgery.Event.Capped.CappedTubeExclusion
import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectiveTopology

/-!
# Single-cap and capped-tube exclusions

Both supplied cap kinds have connected noncompact literal carriers.
Consequently neither a single cap nor a capped tube can contain an entire
compact ambient component. These are the noncompact alternatives in the
whole-component application of Appendix A to Proposition 15.3.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- Transfer connectedness through the punctured-projective cap's exact
stored model and its literal inherited topology. -/
theorem projective_cap_connected {p : RealProjectiveThree} {U : Set M}
    (C : CapModelEquivalence .puncturedProjective p U) : IsConnected U := by
  let := C.model_topology
  let e : U ≃ₜ PuncturedRealProjectiveThree p :=
    ((capCarrierHomeomorph C).trans C.standard_model).trans Homeomorph.ulift
  let : ConnectedSpace (PuncturedRealProjectiveThree p) :=
    isConnected_iff_connectedSpace.mp (punctured_projective_connected p)
  let : ConnectedSpace U := e.connectedSpace_iff.mpr inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

/-- Compactness of a projective cap would make its actual punctured model
compact, contradicting the antipodal-complement argument. -/
theorem projective_cap_not_compact {p : RealProjectiveThree} {U : Set M}
    (C : CapModelEquivalence .puncturedProjective p U) : ¬ IsCompact U := by
  intro hU
  let := C.model_topology
  let e : U ≃ₜ PuncturedRealProjectiveThree p :=
    ((capCarrierHomeomorph C).trans C.standard_model).trans Homeomorph.ulift
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hmodel : CompactSpace (PuncturedRealProjectiveThree p) := e.compactSpace
  exact punctured_projective_not_compact p
    (isCompact_iff_compactSpace.mpr hmodel)

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in
/-- Both cap kinds in the frozen certificate are connected. -/
theorem cap_connected (C : CapCertificate g) : IsConnected C.carrier := by
  cases hkind : C.model_kind with
  | euclidean => exact euclidean_cap_connected (hkind ▸ C.model_equivalence)
  | puncturedProjective => exact projective_cap_connected (hkind ▸ C.model_equivalence)

omit [T2Space M] in
/-- Both cap kinds in the frozen certificate are noncompact. -/
theorem cap_not_compact (C : CapCertificate g) : ¬ IsCompact C.carrier := by
  cases hkind : C.model_kind with
  | euclidean => exact euclidean_cap_not_compact (hkind ▸ C.model_equivalence)
  | puncturedProjective => exact projective_cap_not_compact (hkind ▸ C.model_equivalence)

/-- A single cap cannot contain a whole compact ambient component. -/
theorem no_cap_containing_compact_component
    (x : M) (hx : IsCompact (connectedComponent x)) (C : CapCertificate g) :
    ¬ connectedComponent x ⊆ C.carrier := by
  intro hsub
  have heq : C.carrier = connectedComponent x :=
    Set.Subset.antisymm
      ((cap_connected C).subset_connectedComponent (hsub mem_connectedComponent)) hsub
  exact cap_not_compact C (heq.symm ▸ hx)

/-- Discharge the noncompact-cap hypothesis for either actual capped-tube kind. -/
theorem capped_tube_not_compact_of_model (C : CappedTubeCertificate g) :
    ¬ IsCompact C.carrier := capped_tube_not_compact C (cap_not_compact C.cap)

/-- Neither cap kind allows a capped tube to contain a whole compact component. -/
theorem no_capped_tube_model_containing_compact_component
    (x : M) (hx : IsCompact (connectedComponent x)) (C : CappedTubeCertificate g) :
    ¬ connectedComponent x ⊆ C.carrier :=
  no_capped_tube_containing_compact_component x hx C (cap_not_compact C.cap)

end PoincareMT.M38
