import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]

theorem flow_eq_exp_smul_of_radial_field
    {Y : (x : M) → TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    {Φ : ℝ → M → M} (hzero : ∀ x, Φ 0 x = x)
    (horbit : ∀ x, IsMIntegralCurve (I := I) (fun t => Φ t x) Y)
    {e : E → M} {r : ℝ}
    (he : ContMDiffOn 𝓘(ℝ, E) I ∞ e (ball (0 : E) r))
    (hradial : ∀ v ∈ ball (0 : E) r, Y (e v) = mfderiv 𝓘(ℝ, E) I e v v) :
    ∀ t ≤ 0, ∀ v ∈ ball (0 : E) r, Φ t (e v) = e (Real.exp t • v) := by
  intro t ht v hv
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, Real.exp s • v ∈ ball (0 : E) r := by
    apply (Real.continuous_exp.smul continuous_const).continuousAt.preimage_mem_nhds
    exact isOpen_ball.mem_nhds (by
      change Real.exp 0 • v ∈ ball (0 : E) r
      simpa only [Real.exp_zero, one_smul] using hv)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε : ℝ := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hεball : Real.exp ε • v ∈ ball (0 : E) r :=
    hδball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      (half_lt_self hδ : δ / 2 < δ))
  have hball (s : ℝ) (hs : s < ε) : Real.exp s • v ∈ ball (0 : E) r := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (Real.exp_pos s).le]
    have hεnorm : Real.exp ε * ‖v‖ < r := by
      simpa only [mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (Real.exp_pos ε).le] using hεball
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hs.le)
      (norm_nonneg v)).trans_lt hεnorm
  have hcurve : IsMIntegralCurveOn (I := I) (fun s => e (Real.exp s • v)) Y
      (Ioo (t - 1) ε) := by
    intro s hs
    have hev := he.contMDiffAt (isOpen_ball.mem_nhds (hball s hs.2))
    have hds : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => Real.exp u • v) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Real.exp s • v)) :=
      ((Real.hasDerivAt_exp s).smul_const v).hasFDerivAt.hasMFDerivAt
    have hd := (hev.mdifferentiableAt (by simp)).hasMFDerivAt.comp s hds
    have hmap :
        (mfderiv 𝓘(ℝ, E) I e (Real.exp s • v)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Real.exp s • v)) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (Y (e (Real.exp s • v))) := by
      ext
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        map_smul, hradial _ (hball s hs.2)]
    rw [hmap] at hd
    exact hd.hasMFDerivWithinAt
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (show (0 : ℝ) ∈ Ioo (t - 1) ε from ⟨by linarith, hε⟩)
    (hY.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
    ((horbit (e v)).isMIntegralCurveOn (Ioo (t - 1) ε)) hcurve
    (by simp only [hzero, Real.exp_zero, one_smul])
  exact heq (show t ∈ Ioo (t - 1) ε from ⟨by linarith, ht.trans_lt hε⟩)

end Poincare.Manifold
