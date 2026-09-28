import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.LengthVariation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem exists_right_endpoint_distance_increment_bound
    (F : RicciFlow n M J) {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    {t : ℝ} (hflow : -t ∈ interior J) (ht : t ∈ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      ((F.metric (-s)).edist (γ t) (γ s)).toReal ≤
        ((F.metric (-t)).tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) + ε) *
          (s - t) := by
  have hcont := F.continuousAt_curve_speed hI hγ hflow ht
  obtain ⟨d, hd, hclose⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hI t ht
  refine ⟨min d r / 2, by positivity, ?_⟩
  intro s hs
  have hs0 : 0 ≤ s - t := sub_nonneg.mpr hs.1
  have hsd : s - t < d := by linarith [min_le_left d r, hs.2]
  have hsr : s - t < r := by linarith [min_le_right d r, hs.2]
  have hsub : Icc t s ⊆ I := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)]
    linarith [hu.2]
  have hbound (u : ℝ) (hu : u ∈ Icc t s) :
      (F.metric (-s)).tangentNorm (γ u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) ≤
        (F.metric (-t)).tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) + ε := by
    have hdu : dist (-s, u) (-t, t) < d := by
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · simpa only [dist_neg_neg, Real.dist_eq, abs_of_nonneg hs0] using hsd
      · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)]
        linarith [hu.2]
    have h := hclose hdu
    rw [Real.dist_eq] at h
    exact le_of_lt (by linarith [(abs_lt.mp h).2])
  apply ((F.metric (-s)).toReal_edist_le_integral_speed hs.1 hI hsub hγ).trans
  calc
    _ ≤ ∫ _u in t..s,
        (F.metric (-t)).tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) + ε :=
      intervalIntegral.integral_mono_on hs.1
        (((F.metric (-s)).continuousOn_speed_of_contMDiffOn hI hγ).mono hsub
          |>.intervalIntegrable_of_Icc hs.1) intervalIntegrable_const hbound
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

end PoincareConjecture.RicciFlow
