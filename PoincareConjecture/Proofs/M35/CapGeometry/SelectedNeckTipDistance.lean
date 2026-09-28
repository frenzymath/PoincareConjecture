import PoincareConjecture.Proofs.M35.CapGeometry.SelectedFullStaticNeck
import PoincareConjecture.Proofs.M35.CapGeometry.NeckTipDistance
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => StandardCapSpace

theorem blowupSequence_selected_neck_tip_distance :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (P : M35StandardCapPredecessors)
      {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
      (t : ℕ → ℝ) (x : ℕ → V)
      (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
      (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
      (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
        (blowupBackwardInterval ⊤)),
      letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
      letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
      letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
      ∀ (N : EpsilonNeck (L.limit.flow.metric 0)), N.epsilon ≤ delta →
        N.connection = L.limit.flow.connection 0 → IsCompact (closure N.carrier) →
        ∀ j : ℕ, closure N.carrier ⊆ L.exhaustion.space j →
        ∀ᶠ k in atTop,
          let y := ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ N.center).val
          N.epsilon⁻¹ / 4 ≤ ((E.flow.metric (t (L.subsequence k))).edist 0 y).toReal *
            Real.sqrt ((E.flow.connection (t (L.subsequence k))).scalarCurvature y) := by
  obtain ⟨delta, hdelta, htip⟩ := exists_static_neck_tip_distance_threshold
  refine ⟨min delta (1 / 24), lt_min hdelta (by norm_num), ?_⟩
  intro P g₀ E t x ht hR L
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro N he hconnection hcompact j hstage
  have hclose := blowupSequence_full_static_neck_close P E t x ht hR L N
    (he.trans (min_le_right _ _)) hconnection hcompact j hstage
  filter_upwards [hclose, eventually_ge_atTop j] with k hk hjk
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  let phi := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime
  have hsub : N.carrier ⊆ phi.source :=
    subset_closure.trans (hstage.trans (L.exhaustion.space_increasing hjk))
  let M := N.transportedStandardPatch phi hsub
  let S : StandardStaticNeck E.atlas (E.flow.metric (t (L.subsequence k)))
      (E.flow.connection (t (L.subsequence k))) N.epsilon := {
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    center := phi N.center
    scalar_pos := E.scalar_pos (ht _) _
    patch := M
    close := hk
  }
  exact htip N.epsilon N.epsilon_pos (he.trans (min_le_left _ _)) E.atlas
    (E.flow.metric (t (L.subsequence k))) (E.flow.connection (t (L.subsequence k)))
    (E.rotation_invariant _ (ht _)) S

end PoincareConjecture.M35.OrdinaryRealization
