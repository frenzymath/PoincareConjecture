import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.ConnectingRicci
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.LengthVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem exists_backward_distance_upper_support
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) (hxy : x ≠ y)
    {τ B scale : ℝ} (hτ : 0 < τ) (hscale : 0 < scale)
    (hx : reducedLength K.flow 0 p x τ ≤ B)
    (hy : reducedLength K.flow 0 p y τ ≤ B) :
    ∃ (u : ℝ → ℝ) (d : ℝ),
      u τ = ((K.flow.metric (-τ)).edist x y).toReal ∧
      (∀ s, ((K.flow.metric (-s)).edist x y).toReal ≤ u s) ∧
      HasDerivAt u d τ ∧
      d ≤ 2 * (n : ℝ) * scale + 24 * B / (τ * scale) +
        576 / (τ ^ 2 * scale ^ 3) := by
  let g := K.flow.metric (-τ)
  let c := (g.edist x y).toReal
  have hc : 0 < c := by
    let := g.toMetricSpace
    exact dist_pos.mpr hxy
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete (K.complete (-τ) (by linarith)) x y
  have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-ε) (1 + ε)) :=
    fun s hs => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ hs).contMDiffWithinAt
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hzero := hsub (show (0 : ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at hzero x (by
    simpa only [hγ0] using mem_extChartAt_source x)).1
  have hC0 : g.tangentNorm x (deriv (fun s => extChartAt (𝓡 n) x (γ s)) 0) = C := by
    simpa only [RiemannianMetric.chartCoefficients_self, RiemannianMetric.tangentNorm] using
      (hγ.tangentNorm_initial hzero hγ0 hv).symm.trans (hC 0 hzero)
  have hCc : (C : ℝ) = c := by
    have h := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    rw [hC0] at h
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ (C : ℝ) from C.2)] using
      congrArg ENNReal.toReal h
  have hspeed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c := by
    exact (hC s (hsub hs)).trans hCc
  let u : ℝ → ℝ := fun s => ∫ a in (0 : ℝ)..1,
    (K.flow.metric (-s)).tangentNorm (γ a) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ a 1)
  let d : ℝ := ∫ a in (0 : ℝ)..1, (K.flow.connection (-τ)).ricci (γ a)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ a 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ a 1) / c
  have htime : -τ ∈ interior (Iic (0 : ℝ)) := by
    rw [interior_Iic]
    exact neg_neg_of_pos hτ
  have hder := K.flow.hasDerivAt_integral_speed zero_le_one isOpen_Ioo hsub
    hγsmooth htime (by
      intro a ha heq
      have hs := hspeed a ha
      rw [heq, RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero] at hs
      exact hc.ne' hs.symm)
  have hd : HasDerivAt u d τ := by
    have h := hder.comp τ (hasDerivAt_neg τ)
    apply h.congr_deriv
    rw [mul_neg_one, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le zero_le_one] at ha
    have hs := hspeed a ha
    change (K.flow.metric (-τ)).tangentNorm _ _ = c at hs
    simp only [hs, neg_div, neg_neg]
  refine ⟨u, d, ?_, ?_, hd, ?_⟩
  · change (∫ a in (0 : ℝ)..1, _) = _
    calc
      _ = ∫ _a in (0 : ℝ)..1, c := intervalIntegral.integral_congr (fun a ha => by
        exact hspeed a (by simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ha))
      _ = _ := by simp [c, g]
  · intro s
    have h := (K.flow.metric (-s)).toReal_edist_le_integral_speed zero_le_one
      isOpen_Ioo hsub hγsmooth
    simpa only [hγ0, hγ1] using h
  · have hmin' : g.edist (γ 0) (γ 1) = ENNReal.ofReal (1 * c) := by
      rw [hγ0, hγ1, one_mul]
      exact (ENNReal.ofReal_toReal (g.edist_ne_top x y)).symm
    have h := P.connecting_geodesic_ricci_integral_le p hτ isOpen_Ioo hsub
      (by simpa only [zero_sub] using hγ) zero_le_one hc
      (by simpa only [zero_sub] using hspeed)
      (by simpa only [zero_sub] using hmin') hscale (by simpa only [hγ0] using hx)
      (by simpa only [hγ1] using hy)
    convert! h using 1
    dsimp only [d]
    congr 1
    ext a
    rw [zero_sub]

theorem exists_backward_distance_upper_support_at_pair
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M)
    {τ B scale : ℝ} (hτ : 0 < τ) (hscale : 0 < scale)
    (hx : reducedLength K.flow 0 p x τ ≤ B)
    (hy : reducedLength K.flow 0 p y τ ≤ B) :
    ∃ (u : ℝ → ℝ) (d : ℝ),
      u τ = ((K.flow.metric (-τ)).edist x y).toReal ∧
      (∀ s, ((K.flow.metric (-s)).edist x y).toReal ≤ u s) ∧
      HasDerivAt u d τ ∧
      d ≤ 2 * (n : ℝ) * scale + 24 * B / (τ * scale) +
        576 / (τ ^ 2 * scale ^ 3) := by
  by_cases hxy : x = y
  · subst y
    have hB := (P.reducedLength_pos p x τ hτ).le.trans hx
    refine ⟨fun _ => 0, 0, ?_, ?_, hasDerivAt_const τ 0, by positivity⟩
    · let := (K.flow.metric (-τ)).toMetricSpace
      exact (dist_self x).symm
    · intro s
      let := (K.flow.metric (-s)).toMetricSpace
      exact (dist_self x).le
  · exact P.exists_backward_distance_upper_support p x y hxy hτ hscale hx hy

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
