import PoincareConjecture.Proofs.M35.CapGeometry.RadiusSize
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapScalar

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem blowupSequence_cap_curvature_ball_volume_lower (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (NC : StandardFlowNoncollapsingCertificate E.flow)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (htone : Tendsto t atTop (𝓝 1))
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      ∀ᶠ k in atTop,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        ∀ y ∈ closure N.carrier, ∀ r : ℝ, 0 < r →
          scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
            (E.flow.connection (t (L.subsequence k)))
              ((E.flow.metric (t (L.subsequence k))).ball (f y) r) = r⁻¹ ^ 2 →
          ENNReal.ofReal (NC.kappa / 8 * r ^ 3) ≤
            calibratedMetricVolume (E.flow.metric (t (L.subsequence k)))
              ((E.flow.metric (t (L.subsequence k))).ball (f y) r) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro N hconnection hcompact hU
  obtain ⟨a, _, _, ha, _, _, _, k₀, _, hfloor⟩ :=
    blowupSequence_cap_scalar_control P E t x ht hR L j N hconnection hcompact hU
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : Tendsto Q atTop atTop := by
    simpa only [Q, blowupSequence_scale, Function.comp_def] using
      hR.comp L.subsequence_strictMono.tendsto_atTop
  have hhigh := (Tendsto.const_mul_atTop ha hQ).eventually
    (eventually_ge_atTop (max (NC.radius⁻¹ ^ 2) 2))
  have htime := (htone.comp L.subsequence_strictMono.tendsto_atTop).eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop k₀, hhigh, htime] with k hk hhighk htk
  dsimp only
  intro y hy r hr hscale
  apply E.scalar_curvature_ball_volume_lower_of_large_scalar P.curvature NC
    (ht (L.subsequence k)) htk.le hr _ hscale
  exact hhighk.trans ((hfloor k hk).1 y hy).1

end PoincareConjecture.M35.OrdinaryRealization
