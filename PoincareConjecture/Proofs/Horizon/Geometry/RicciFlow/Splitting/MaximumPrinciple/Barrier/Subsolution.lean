import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.MetricBump

noncomputable section
open Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

open Barrier

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chartBump_subsolution {g : ℝ → RiemannianMetric n M}
    (conn : ∀ t, LeviCivitaData (g t)) (α : M)
    {rho lam Lam H₀ : ℝ} (a : ℝ)
    (hrho : 0 < rho) (hlam : 0 < lam) (hLam : lam ≤ Lam) (hH₀ : 0 ≤ H₀)
    {gamma : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ} {velocity : EuclideanSpace ℝ (Fin n)}
    (hg : HasDerivAt gamma velocity t) {x : M}
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) α).source)
    (hbounds : 0 < ballGap rho (gamma t) (extChartAt (𝓡 n) α x) →
      lam * ‖extChartAt (𝓡 n) α x - gamma t‖ ^ 2 ≤
          radialQuadratic (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t) ∧
        radialQuadratic (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t) ≤
          Lam * ‖extChartAt (𝓡 n) α x - gamma t‖ ^ 2 ∧
        radialTrace (g t) α (extChartAt (𝓡 n) α x) +
          radialDrift (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t) +
          ⟪extChartAt (𝓡 n) α x - gamma t, velocity⟫_ℝ ≤ H₀) :
    deriv (chartBump α rho (dampingConstant rho lam Lam H₀) a gamma x) t ≤
      (conn t).laplacian
        (fun z => chartBump α rho (dampingConstant rho lam Lam H₀) a gamma z t)
        x := by
  apply sub_nonneg.mp
  rw [chart_heat_residual conn α rho (dampingConstant rho lam Lam H₀) a hg hx]
  apply mul_nonneg (Real.exp_pos _).le
  let s := ballGap rho (gamma t) (extChartAt (𝓡 n) α x)
  let Q := radialQuadratic (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t)
  let J := radialTrace (g t) α (extChartAt (𝓡 n) α x) +
    radialDrift (g t) α (extChartAt (𝓡 n) α x) (extChartAt (𝓡 n) α x - gamma t) +
    ⟪extChartAt (𝓡 n) α x - gamma t, velocity⟫_ℝ
  change 0 ≤ dampingConstant rho lam Lam H₀ * expNegInvGlue s +
    4 * profileSecond s * Q - 2 * profileFirst s * J
  by_cases hs : 0 < s
  · obtain ⟨hlo, hhi, hJ⟩ := hbounds hs
    have hsrho : s ≤ rho ^ 2 := by dsimp [s, ballGap]; nlinarith [sq_nonneg ‖extChartAt (𝓡 n) α x - gamma t‖]
    have hr2 : ‖extChartAt (𝓡 n) α x - gamma t‖ ^ 2 = rho ^ 2 - s := by
      dsimp [s, ballGap]
      ring
    have hcoef := radial_coefficient_nonneg_of_radius_sq hrho hlam hLam hH₀
      hs hsrho hr2 hlo hhi hJ
    have hcoef' : 0 ≤ dampingConstant rho lam Lam H₀ +
        4 * Q * s⁻¹ ^ 4 - 8 * Q * s⁻¹ ^ 3 - 2 * J * s⁻¹ ^ 2 := by
      simpa only [div_eq_mul_inv, inv_pow] using hcoef
    have hid : dampingConstant rho lam Lam H₀ * expNegInvGlue s +
        4 * profileSecond s * Q - 2 * profileFirst s * J =
        (dampingConstant rho lam Lam H₀ +
          4 * Q * s⁻¹ ^ 4 - 8 * Q * s⁻¹ ^ 3 - 2 * J * s⁻¹ ^ 2) *
            expNegInvGlue s := by
      unfold profileFirst profileSecond
      ring
    rw [hid]
    exact mul_nonneg hcoef' (expNegInvGlue.nonneg _)
  · have hz := expNegInvGlue.zero_of_nonpos (le_of_not_gt hs)
    simp [profileFirst, profileSecond, hz]

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
