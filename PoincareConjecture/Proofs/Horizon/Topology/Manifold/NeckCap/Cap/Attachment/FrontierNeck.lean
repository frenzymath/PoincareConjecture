import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.EndSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.CoreAvoidance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.EndFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.FrontierQuarter

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_frontier_neck_overlap_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g) (P : EpsilonNeck g), C.epsilon ≤ ε₀ →
          P.epsilon = C.epsilon → P.center ∈ frontier C.carrier →
          ∃ Q : EpsilonNeck g, Q.SameUpToReversal P ∧ Q.IsSeparating ∧
            Disjoint C.closed_core Q.carrier ∧
            C.carrier ∩ Q.carrier = C.end_neck.carrier ∩ Q.carrier ∧
            C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹ ⊆ Q.carrier ∧
            Q.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆
              C.end_neck.region (-(0.2 : ℝ) * C.epsilon⁻¹) ((0.6 : ℝ) * C.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, hsmall, hseparate⟩ := exists_end_neck_separating_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hfrontier⟩ := exists_frontier_carrier_subset_closure_positive_end.{u}
  obtain ⟨ε₃, hε₃, _, hquarter⟩ := EpsilonNeck.exists_frontier_reversal_quarter_overlap.{u}
  obtain ⟨ε₄, hε₄, _, havoid⟩ := exists_frontier_neck_disjoint_closed_core_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)), lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C P hε heq hp
  have hNsep := hseparate C (hε.trans (min_le_left _ _))
  have hcontact := hfrontier C (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) hp
  have hout : P.center ∉ C.end_neck.carrier := by
    have hf := C.frontier_carrier_subset_frontier_end hp
    rw [C.end_neck.carrier_open.frontier_eq] at hf
    exact hf.2
  obtain ⟨Q, hQ, hpos, hneg, hsep, _⟩ := hquarter C.end_neck P
    (C.end_neck_epsilon.trans_le (hε.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
    (heq.trans C.end_neck_epsilon.symm)
    (by simpa only [C.end_neck_epsilon] using hcontact) hout
  have hsame : Q.SameUpToReversal P := by
    rcases hQ with rfl | rfl
    · exact EpsilonNeck.SameUpToReversal.refl _
    · exact P.reversed_sameUpToReversal
  have hdis : Disjoint C.closed_core Q.carrier := by
    rw [hsame.carrier_eq]
    exact havoid C P (hε.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))) heq hp
  refine ⟨Q, hsame, hsep.mpr hNsep, hdis, ?_, ?_, ?_⟩
  · rw [C.carrier_eq_closed_core_union_end, union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp hdis, empty_union]
  · simpa only [C.end_neck_epsilon] using hpos
  · simpa only [C.end_neck_epsilon] using hneg

end PoincareConjecture.CapCertificate
