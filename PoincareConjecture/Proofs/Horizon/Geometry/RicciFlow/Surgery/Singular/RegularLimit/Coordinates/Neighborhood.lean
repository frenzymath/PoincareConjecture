import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.DerivativeControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.MetricLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.LocalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false

open Set Filter Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_uniform_coordinate_neighborhood
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {q : M} (hq : q ∈ H.reference.regularLimitSet) :
    ∃ s r a b : ℝ, H.reference.tMinus < s ∧ s < T ∧
      0 < r ∧ 0 < a ∧ 0 ≤ b ∧
      let c := extChartAt (𝓡 3) q
      Metric.closedBall (c q) r ⊆ c.target ∧
      c.symm '' Metric.closedBall (c q) r ⊆ H.reference.regularLimitSet ∧
      (∀ t ∈ Ico s T, ∀ z ∈ Metric.closedBall (c q) r, ∀ v,
        a * ‖v‖ ^ 2 ≤ (H.reference.flow.metric t).pullbackCoefficients c.symm z v v ∧
        (H.reference.flow.metric t).pullbackCoefficients c.symm z v v ≤ b * ‖v‖ ^ 2) ∧
      (∀ k : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ico s T,
        ∀ z ∈ Metric.closedBall (c q) r,
          (H.reference.flow.connection t).curvatureDerivativeNorm k (c.symm z) ≤ K) := by
  obtain ⟨s, U, hs, hsT, hU, hqU, hUreg, hder⟩ :=
    H.exists_open_uniform_curvature_derivative_tail P04 hq
  obtain ⟨r₀, C, hr₀, hC, htarget, _, hell⟩ :=
    (H.reference.flow.metric s).exists_compact_coordinate_ellipticity q
  let c := extChartAt (𝓡 3) q
  have hcont : ContinuousAt c.symm (c q) := continuousAt_extChartAt_symm q
  have hpre : c.symm ⁻¹' U ∈ 𝓝 (c q) := hcont.preimage_mem_nhds
    (by simpa [c] using hU.mem_nhds hqU)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hpre
  let r := min r₀ r₁
  have hsmall : Metric.closedBall (c q) r ⊆ Metric.closedBall (c q) r₀ :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hsub : ∀ z ∈ Metric.closedBall (c q) r, c.symm z ∈ U := by
    intro z hz
    exact hball (Metric.closedBall_subset_closedBall (min_le_right _ _) hz)
  obtain ⟨K, hK, hbound⟩ := hder 0
  let L := Real.exp (-2 * (3 : ℝ) * K * (T - s))
  let B := Real.exp (2 * (3 : ℝ) * K * (T - s))
  have hL : 0 < L := Real.exp_pos _
  have hB : 0 < B := Real.exp_pos _
  refine ⟨s, r, L / C ^ 2, B * C ^ 2, hs, hsT, lt_min hr₀ hr₁,
    div_pos hL (sq_pos_of_pos hC), by positivity, ?_, ?_, ?_, ?_⟩
  · exact fun z hz => htarget (hsmall hz)
  · rintro _ ⟨z, hz, rfl⟩
    exact hUreg (hsub z hz)
  · intro t ht z hz v
    let w := mfderiv (𝓡 3) (𝓡 3) c.symm z v
    have hnorm := hell z (hsmall hz) v
    have hpos : 0 ≤ (H.reference.flow.metric s).inner (c.symm z) w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact ((H.reference.flow.metric s).pos _ w hw).le
    have hsq : ((H.reference.flow.metric s).tangentNorm (c.symm z) w) ^ 2 =
        (H.reference.flow.metric s).inner (c.symm z) w w := Real.sq_sqrt hpos
    have hlo : ‖v‖ ^ 2 ≤ C ^ 2 * (H.reference.flow.metric s).inner (c.symm z) w w := by
      have h := sq_le_sq₀ (norm_nonneg v)
        (mul_nonneg hC.le (Real.sqrt_nonneg _)) |>.mpr hnorm.1
      rw [← hsq]
      simpa only [mul_pow, RiemannianMetric.tangentNorm, c, w] using h
    have hhi : (H.reference.flow.metric s).inner (c.symm z) w w ≤ C ^ 2 * ‖v‖ ^ 2 := by
      have h := sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg hC.le (norm_nonneg v)) |>.mpr hnorm.2
      rw [← hsq]
      simpa only [mul_pow, RiemannianMetric.tangentNorm, c, w] using h
    have hcurv : ∀ τ ∈ Ico s T,
        (H.reference.flow.connection τ).curvatureTensorNorm (c.symm z) ≤ K := by
      intro τ hτ
      rw [← P04.curvature_norm_zero 3 M (H.reference.flow.metric τ)
        (H.reference.flow.connection τ)]
      exact hbound τ hτ (c.symm z) (hsub z hz)
    have htime := RicciFlowAnalysis.metric_diagonal_bounds_on_tail
      H.reference.flow hs.le hsT hK.le (c.symm z) hcurv w ht
    change L / C ^ 2 * ‖v‖ ^ 2 ≤ (H.reference.flow.metric t).inner (c.symm z) w w ∧
      (H.reference.flow.metric t).inner (c.symm z) w w ≤ B * C ^ 2 * ‖v‖ ^ 2
    constructor
    · calc
        L / C ^ 2 * ‖v‖ ^ 2 = L * (‖v‖ ^ 2 / C ^ 2) := by ring
        _ ≤ L * (H.reference.flow.metric s).inner (c.symm z) w w :=
          mul_le_mul_of_nonneg_left ((div_le_iff₀ (sq_pos_of_pos hC)).mpr
            (by simpa only [mul_comm] using hlo)) hL.le
        _ ≤ _ := htime.1
    · calc
        _ ≤ B * (H.reference.flow.metric s).inner (c.symm z) w w := htime.2
        _ ≤ B * (C ^ 2 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hhi hB.le
        _ = _ := by ring
  · intro k
    obtain ⟨D, hD, hDbound⟩ := hder k
    exact ⟨D, hD, fun t ht z hz => hDbound t ht (c.symm z) (hsub z hz)⟩

end PoincareConjecture.SingularTimeAssumptions
