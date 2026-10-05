import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.MixedOverlap
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Boundary
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Overlap

/-!
# Closing noncontaining caps at a core-frontier contact

The boundary-disjoint case forces containment, the boundary-contained case
closes by enclosing one complementary side, and mixed boundary overlap closes
by aligning whole shifted spheres. The resulting compact component is exactly
the union of the two original cap carriers.

Reference: Morgan--Tian, Claims A.23--A.24, pp. 512--513.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

/-- Original equal-parameter caps close at a core-frontier contact whenever
the contacting cap does not contain the first cap. -/
theorem exists_frontier_contact_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
          (frontier C.carrier ∩ D.core).Nonempty →
          (¬ C.carrier ⊆ D.carrier) →
          C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
            IsCompact (C.carrier ∪ D.carrier) := by
  obtain ⟨ε₀, hε₀, hsmall, hmixed⟩ := exists_mixed_overlap_containment_or_closing_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hC hDC hcontact hnoncontain
  by_cases hmeet : (D.boundary_sphere ∩ C.carrier).Nonempty
  · by_cases hcontained : D.boundary_sphere ⊆ C.carrier
    · apply C.compact_component_of_boundary_subset D hcontained
      obtain ⟨x, hx, hxD⟩ := hcontact
      exact ⟨x, hx, D.core_subset_closed_core hxD⟩
    · exact (hmixed C D hC hDC hmeet hcontained).resolve_left hnoncontain
  · have hdis : Disjoint C.carrier D.boundary_sphere :=
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet)).symm
    have hcore := D.subset_core_of_disjoint_boundary_of_frontier_core_contact
      C.isConnected_carrier.isPreconnected hdis hcontact
    exact False.elim (hnoncontain (hcore.trans D.core_subset_carrier))

end PoincareMT.CapCertificate
