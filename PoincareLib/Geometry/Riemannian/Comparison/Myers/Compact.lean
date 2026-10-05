import PoincareLib.Geometry.Riemannian.Comparison.Myers.Segment
import PoincareLib.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareLib.Geometry.Riemannian.Distance.SegmentSpeed

/-!
# Bonnet--Myers compactness

A uniform positive Ricci lower bound bounds the length of every minimizing
segment. Metric completeness gives compact closed balls, so the whole connected
manifold is compact. The polynomial index test gives a nonsharp diameter bound.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

/-- The polynomial Bonnet--Myers estimate for the intrinsic squared distance. -/
theorem ricci_mul_edist_sq_le (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ}
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), k * g.inner x v v ≤ D.ricci x v v)
    (p x : M) : k * (g.edist p x).toReal ^ 2 ≤ 10 * (n : ℝ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let L := (g.edist p x).toReal
  by_cases hL : 0 < L
  · obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
      g.exists_minimizing_geodesic_of_metricComplete hc p x
    have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have h0 := hI (show (0 : ℝ) ∈ Icc 0 1 by simp)
    obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
    have hv := (hγ.hasDerivAt_chart_at h0 p (by
      simpa only [hγ0] using mem_extChartAt_source p)).1
    have hC0 : g.tangentNorm p (deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0) = C := by
      simpa only [chartCoefficients_self, tangentNorm] using
        (hγ.tangentNorm_initial h0 hγ0 hv).symm.trans (hC 0 h0)
    have hCL : (C : ℝ) = L := by
      have h := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
      rw [hC0] at h
      simpa only [ENNReal.toReal_ofReal (show 0 ≤ (C : ℝ) from C.2)] using
        congrArg ENNReal.toReal h
    have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = L := by
      rw [← hCL]
      exact hC t (hI ht)
    apply ConjugateFrame.ricci_mul_speed_sq_le_of_minimizing D hε hγ hL hspeed
    · rw [hγ0, hγ1]
      exact (ENNReal.ofReal_toReal (g.edist_ne_top p x)).symm
    · intro t ht
      have hsq := congrArg (fun r : ℝ => r ^ 2) (hspeed t ht)
      have hnonneg : 0 ≤ g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
        change 0 ≤ inner ℝ (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        exact real_inner_self_nonneg
      rw [tangentNorm, Real.sq_sqrt hnonneg] at hsq
      rw [← hsq]
      exact hRic _ _
  · have hz : L = 0 := le_antisymm (le_of_not_gt hL) ENNReal.toReal_nonneg
    change k * L ^ 2 ≤ _
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    positivity

/-- A complete connected manifold with a uniform positive Ricci lower bound
has finite intrinsic diameter. -/
theorem edist_le_of_positive_ricci (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ} (hk : 0 < k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), k * g.inner x v v ≤ D.ricci x v v)
    (p x : M) : g.edist p x ≤ ENNReal.ofReal (Real.sqrt (10 * (n : ℝ) / k)) := by
  have hsq : (g.edist p x).toReal ^ 2 ≤ 10 * (n : ℝ) / k := by
    apply (le_div_iff₀ hk).mpr
    simpa only [mul_comm] using g.ricci_mul_edist_sq_le D hc hRic p x
  rw [← ENNReal.ofReal_toReal (g.edist_ne_top p x)]
  apply ENNReal.ofReal_le_ofReal
  exact (Real.le_sqrt ENNReal.toReal_nonneg (by positivity)).mpr hsq

/-- Bonnet--Myers compactness from metric completeness and positive Ricci
curvature. -/
theorem compactSpace_of_positive_ricci (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {k : ℝ} (hk : 0 < k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), k * g.inner x v v ≤ D.ricci x v v) :
    CompactSpace M := by
  cases isEmpty_or_nonempty M with
  | inl h => exact ⟨by simp⟩
  | inr h =>
    obtain ⟨p⟩ := h
    have heq : {x | g.edist p x ≤ ENNReal.ofReal (Real.sqrt (10 * (n : ℝ) / k))} =
        (univ : Set M) := by
      exact Set.eq_univ_of_forall fun x => g.edist_le_of_positive_ricci D hc hk hRic p x
    constructor
    rw [← heq]
    exact g.isCompact_closedBall_of_metricComplete hc p _

end PoincareMT.RiemannianMetric
