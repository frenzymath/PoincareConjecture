import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.SameCoreTopology








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_same_core_boundary_region_subset_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
      ∀ b r : ℝ, -C.epsilon⁻¹ < b → b < -C.epsilon⁻¹ / 2 → 0 < r →
        r < (0.9 : ℝ) * (C.epsilon⁻¹ + b) - 5 * Real.pi →
        C.boundary_neck.region (-r) r ⊆
          C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b := by
  obtain ⟨ε₁, hε₁, hsmall, hdomain⟩ := exists_truncated_core_domain_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hheight⟩ := EpsilonNeck.exists_frontier_transition_height_bounds.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε b r hb hb' hr hclear
  have hL := inv_pos.mpr C.epsilon_pos
  have hbL : b < C.epsilon⁻¹ := by linarith
  have hrL : r ≤ C.epsilon⁻¹ := by linarith [Real.pi_pos]
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) b)
  let V := C.boundary_neck.region (-r) r
  obtain ⟨hK, _, hI, hfront, _, hcoreI⟩ :=
    hdomain C (hε.trans (min_le_left _ _)) b ⟨hb, hbL⟩
  change IsCompact K at hK
  change interior K = _ at hI
  change frontier K = _ at hfront
  change C.closed_core ⊆ interior K at hcoreI
  have hxB : C.boundary_neck.center ∈ C.boundary_sphere :=
    C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
  have hxfront : C.boundary_neck.center ∈ frontier C.end_neck.reversed.carrier := by
    exact (C.boundary_eq_end_frontier ▸ hxB).2
  have hxnegative : C.boundary_neck.center ∈ closure (C.end_neck.reversed.region
      (C.end_neck.reversed.epsilon⁻¹ / 2) C.end_neck.reversed.epsilon⁻¹) := by
    simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
      C.end_neck_epsilon, neg_div] using C.boundary_subset_negative_end_closure hxB
  obtain ⟨σ, hσ, hσheight⟩ := hheight C.end_neck.reversed C.boundary_neck
    (by simpa only [EpsilonNeck.reversed_epsilon, C.end_neck_epsilon] using
      hε.trans (min_le_right _ _))
    (by rw [EpsilonNeck.reversed_epsilon, C.boundary_neck_epsilon, C.end_neck_epsilon])
    C.boundary_neck.center hxfront hxnegative C.boundary_neck.center_on_central_sphere
  have havoid : Disjoint V (frontier K) := by
    rw [disjoint_left]
    intro y hy hyfront
    rw [hfront] at hyfront
    obtain ⟨q, rfl⟩ := hyfront
    have hz := (hσheight q (-b)
      (by rw [EpsilonNeck.reversed_epsilon, C.end_neck_epsilon]; exact ⟨by linarith, by linarith⟩)).2
    simp only [EpsilonNeck.reversed_coordinate_map, neg_neg,
      EpsilonNeck.reversed_epsilon, C.end_neck_epsilon, sub_neg_eq_add] at hz
    have hylo := hy.2.1
    have hyhi := hy.2.2
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul] at hz <;> linarith
  have hcover : V ⊆ interior K ∪ Kᶜ := by
    intro y hy
    by_cases hyK : y ∈ K
    · left
      by_contra hyn
      exact disjoint_left.mp havoid hy ⟨hK.isClosed.closure_eq.symm ▸ hyK, hyn⟩
    · exact Or.inr hyK
  have hconn : IsPreconnected V :=
    (C.boundary_neck.isConnected_region
      (by rw [C.boundary_neck_epsilon]; exact neg_le_neg hrL)
      (by rw [C.boundary_neck_epsilon]; exact hrL) (by linarith)).isPreconnected
  rcases hconn.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hinside | houtside
  · exact hI ▸ hinside
  · have hxV : C.boundary_neck.center ∈ V := by
      have hx := (C.boundary_neck.mem_central_sphere_iff _).mp C.boundary_neck.center_on_central_sphere
      exact ⟨hx.1, by rw [hx.2]; exact neg_lt_zero.mpr hr, by rw [hx.2]; exact hr⟩
    exact False.elim (houtside hxV (interior_subset (hcoreI (C.boundary_subset_closed_core hxB))))

end PoincareConjecture.CapCertificate
