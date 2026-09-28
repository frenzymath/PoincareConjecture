import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem m23_terminal_ball_volume_le_exp_mul_earlier_ball
    (F : RicciFlow 3 M (Iic 0)) (p : M) {δ B r : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ t ∈ Icc (-δ) 0, ∀ x ∈ (F.metric 0).ball p r,
      (F.connection t).curvatureTensorNorm x ≤ B) :
    (F.metric 0).volumeMeasure ((F.metric 0).ball p r) ≤
      ENNReal.ofReal (Real.exp (27 * B * δ)) ^ 3 *
        (F.metric (-δ)).volumeMeasure
          ((F.metric (-δ)).ball p (Real.exp (27 * B * δ) * r)) := by
  let U := (F.metric 0).ball p r
  let c := Real.exp (27 * B * δ)
  have hc : 0 < c := Real.exp_pos _
  have hzero : (0 : ℝ) ∈ Icc (-δ) 0 := ⟨by linarith, le_rfl⟩
  have hearly : -δ ∈ Icc (-δ) 0 := ⟨le_rfl, neg_nonpos.mpr hδ⟩
  have hRic (t : ℝ) (ht : t ∈ Icc (-δ) 0) (x : M) (hx : x ∈ U)
      (v : TangentSpace (𝓡 3) x) :
      |(F.connection t).ricci x v v| ≤ (27 * B) * (F.metric t).inner x v v := by
    have h := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm x v
    have hv : 0 ≤ (F.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric t).pos x v hv).le
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound t ht x hx) (by norm_num)) hv)
  have hforward (x : M) (hx : x ∈ U) (v : TangentSpace (𝓡 3) x) :
      (F.metric 0).tangentNorm x v ≤ c * (F.metric (-δ)).tangentNorm x v := by
    simpa only [zero_sub, abs_neg, abs_of_nonneg hδ] using
      F.tangentNorm_le_exp_of_ricci_bound (convex_Icc (-δ) 0) (fun _ ht ↦ ht.2)
        x v (27 * B) (fun t ht ↦ hRic t ht x hx v) hearly hzero
  have hbackward (x : M) (hx : x ∈ U) (v : TangentSpace (𝓡 3) x) :
      (F.metric (-δ)).tangentNorm x v ≤ c * (F.metric 0).tangentNorm x v := by
    simpa only [sub_zero, abs_neg, abs_of_nonneg hδ] using
      F.tangentNorm_le_exp_of_ricci_bound (convex_Icc (-δ) 0) (fun _ ht ↦ ht.2)
        x v (27 * B) (fun t ht ↦ hRic t ht x hx v) hzero hearly
  have hsubset : U ⊆ (F.metric (-δ)).ball p (c * r) :=
    (F.metric 0).ball_subset_ball_of_tangentNorm_le (F.metric (-δ)) p r c hc hbackward
  have hU : IsOpen U := by
    let := (F.metric 0).toMetricSpace
    rw [show U = Metric.ball p r from ((F.metric 0).toMetricSpace_ball p r).symm]
    exact Metric.isOpen_ball
  have hvol := (F.metric (-δ)).volumeMeasure_image_le_of_tangentNorm_le
    (F.metric 0) (OpenPartialHomeomorph.refl M) hU (subset_univ U)
    contMDiffOn_id hc (by
      intro x hx v
      change (F.metric 0).tangentNorm x (mfderiv (𝓡 3) (𝓡 3) id x v) ≤ _
      rw [mfderiv_id]
      exact hforward x hx v)
    hU.measurableSet (Subset.refl U)
  change (F.metric 0).volumeMeasure (id '' U) ≤ _ at hvol
  rw [image_id] at hvol
  exact hvol.trans (mul_le_mul_right (MeasureTheory.measure_mono hsubset) _)

namespace NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)




theorem eventually_earlier_ball_volume_lower_bound
    {B ν δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ∀ t : ℝ, t ≤ 0 → ∀ x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r,
        |((S.term k).flow.flow.connection t).curvatureTensorNorm x| ≤ B)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (ν * r ^ 3) ≤ calibratedMetricVolume ((S.term k).flow.flow.metric 0)
        (((S.term k).flow.flow.metric 0).ball (S.term k).base r)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal ((ν / Real.exp (27 * B * δ) ^ 6) * r ^ 3) ≤
        calibratedMetricVolume ((S.term k).flow.flow.metric (-δ))
          (((S.term k).flow.flow.metric (-δ)).ball (S.term k).base r) := by
  intro r hr
  let c := Real.exp (27 * B * δ)
  have hc : 0 < c := Real.exp_pos _
  have hrc : 0 < r / c := div_pos hr hc
  filter_upwards [hbound (r / c) hrc, hvolume (r / c) hrc] with k hk hv
  have htransfer := m23_terminal_ball_volume_le_exp_mul_earlier_ball
    (S.term k).flow.flow (S.term k).base hδ
    (r := r / c) (B := B) (fun t ht x hx ↦ (le_abs_self _).trans (hk t ht.2 x hx))
  change ((S.term k).flow.flow.metric 0).volumeMeasure
      (((S.term k).flow.flow.metric 0).ball (S.term k).base (r / c)) ≤
    ENNReal.ofReal c ^ 3 * ((S.term k).flow.flow.metric (-δ)).volumeMeasure
      (((S.term k).flow.flow.metric (-δ)).ball (S.term k).base (c * (r / c))) at htransfer
  rw [mul_div_cancel₀ r hc.ne', ← calibratedMetricVolume_eq_volumeMeasure,
    ← calibratedMetricVolume_eq_volumeMeasure] at htransfer
  have hpow0 : ENNReal.ofReal c ^ 3 ≠ 0 := pow_ne_zero _ (by positivity)
  have hpowtop : ENNReal.ofReal c ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hdiv := (ENNReal.div_le_iff' hpow0 hpowtop).mpr (hv.trans htransfer)
  rw [← ENNReal.ofReal_pow hc.le,
    ← ENNReal.ofReal_div_of_pos (pow_pos hc 3)] at hdiv
  have heq : ν * (r / c) ^ 3 / c ^ 3 = (ν / c ^ 6) * r ^ 3 := by
    field_simp
  rw [heq] at hdiv
  exact hdiv

end NormalizedKappaSolutionSequence

end PoincareConjecture
