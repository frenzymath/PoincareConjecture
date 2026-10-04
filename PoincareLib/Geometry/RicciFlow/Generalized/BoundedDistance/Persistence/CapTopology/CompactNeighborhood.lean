import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.NeckRegions
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Compact neighborhoods of the cap core and a fixed end slab

Morgan--Tian Proposition 9.79, pp. 232-234, and task derivation 10,
section 6. These neighborhoods are obtained by local compactness, without
assuming that the ambient Riemannian distance is complete.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- The closed core and any fixed compact end slab admit one open
neighborhood whose compact closure lies in the actual cap carrier
(Proposition 9.79, pp. 232-234). -/
theorem exists_compact_collar_neighborhood (N : CapCertificate g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    ∃ W : Set M, IsOpen W ∧ N.closed_core ⊆ W ∧
      N.end_neck.coordinate_map '' (univ ×ˢ Icc a b) ⊆ W ∧
      IsCompact (closure W) ∧ closure W ⊆ N.carrier := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  have hc := N.end_neck.isCompact_coordinate_slab_intrinsic
    (by simpa only [N.end_neck_epsilon] using ha)
    (by simpa only [N.end_neck_epsilon] using hb)
  have hslab := N.end_neck.coordinate_slab_subset_carrier_m28
    (by simpa only [N.end_neck_epsilon] using ha)
    (by simpa only [N.end_neck_epsilon] using hb)
  have hcore : N.closed_core ⊆ N.carrier := by
    rw [N.closed_core_eq_complement_end]
    exact sdiff_subset
  obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between
    (N.closed_core_compact.union hc) N.carrier_open
    (union_subset hcore (hslab.trans N.end_neck_subset))
  have hcl : closure (interior L) ⊆ L := hL.isClosed.closure_interior_subset
  exact ⟨interior L, isOpen_interior,
    (subset_union_left.trans hKL), (subset_union_right.trans hKL),
    hL.of_isClosed_subset isClosed_closure hcl, hcl.trans hLV⟩

end PoincareMT.CapCertificate
