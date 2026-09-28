import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength








set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem edist_le_of_tangentNorm_le
    (g : RiemannianMetric n M) {γ : ℝ → M} {I : Set ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (_hC : 0 ≤ C)
    (hspeed : ∀ t ∈ Icc a b,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) ≤ C) :
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal (C * (b - a)) := by
  have hbase := g.edist_le_ofReal_integral_speed hab
    ((hγ.mono hsub).of_le (by simp))
    ((g.continuousOn_speed_of_contMDiffOn hI hγ).mono hsub)
  have hbound : (∫ t in a..b,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) ≤ C * (b - a) := by
    have hcont := (g.continuousOn_speed_of_contMDiffOn hI hγ).mono hsub
    have hfi : IntervalIntegrable
        (fun t => g.tangentNorm (γ t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) volume a b :=
      ContinuousOn.intervalIntegrable (by
        simpa only [uIcc_of_le hab] using hcont)
    have hci : IntervalIntegrable (fun _ : ℝ => C) volume a b :=
      continuousOn_const.intervalIntegrable
    calc
      _ ≤ ∫ _ in a..b, C :=
        intervalIntegral.integral_mono_on hab hfi hci hspeed
      _ = C * (b - a) := by rw [intervalIntegral.integral_const]; ring
  exact hbase.trans (ENNReal.ofReal_le_ofReal hbound)

end PoincareConjecture.RiemannianMetric
