import PoincareLib.Topology.Manifold.NeckCap.Cap.Growth.DistanceGain
import PoincareLib.Topology.Manifold.NeckCap.Cap.Growth.DisjointBoundary
import PoincareLib.Topology.Manifold.NeckCap.Cap.Growth.FrontierDistance
import PoincareLib.Topology.Manifold.NeckCap.Cap.Core.EnclosingRegion

/-!
# Uniform distance gain for a cap-growth step

Nested caps with closed-core contact at the earlier frontier increase the
distance to the complement by a universal multiple of the later collar
scale. Disjoint and mixed boundary positions give the metric gain; full
boundary containment is excluded by the original cap models.

Reference: Morgan--Tian, Claim A.22, pp. 509--511.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.CapCertificate

/-- Every admissible nested cap-growth step has a definite metric gain. -/
theorem exists_nested_frontier_contact_distance_gain :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (C D : CapCertificate g),
        C.epsilon = ε → D.epsilon = ε → C.carrier ⊆ D.carrier →
        (frontier C.carrier ∩ D.closed_core).Nonempty →
        ∀ {p : M}, p ∈ C.carrier →
          (⨅ z ∈ C.carrierᶜ, g.edist p z) +
            ENNReal.ofReal ((0.38 : ℝ) * D.boundary_neck.scale * ε⁻¹) ≤
              ⨅ y ∈ D.carrierᶜ, g.edist p y := by
  obtain ⟨ε₁, hε₁, hsmall, hdisjoint⟩ :=
    exists_disjoint_boundary_core_containment_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hmixed⟩ := exists_frontier_edist_lower_of_mixed_boundary.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε C D hC hD hCD hcontact p hp
  by_cases hdis : Disjoint C.carrier D.boundary_sphere
  · have hcore := hdisjoint hεpos (hε.trans (min_le_left _ _)) C D hC hD hCD hdis
    apply (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)).trans
      (D.complement_distance_gain_of_carrier_subset_core C hcore hp)
    rw [hD]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (0.38 : ℝ) ≤ 0.9) D.boundary_neck.scale_pos.le)
      (inv_pos.mpr hεpos).le
  · have hmeet : (D.boundary_sphere ∩ C.carrier).Nonempty := by
      rw [inter_comm]
      exact not_disjoint_iff_nonempty_inter.mp hdis
    have hmiss := C.not_boundary_subset_of_nested_frontier_contact D hCD hcontact
    apply C.complement_distance_gain_of_frontier_separation D hCD ?_ hp
    intro z hz y hy
    simpa only [hD] using hmixed C D (hC ▸ hε.trans (min_le_right _ _))
      (hD.trans hC.symm) hmeet hmiss hz hy

end PoincareMT.CapCertificate
