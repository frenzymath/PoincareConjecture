import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace Poincare.Analysis.Heat


noncomputable def smoothPositivePart (s : ℝ) : ℝ :=
  ∫ z in 0..s, Real.smoothTransition z

theorem hasDerivAt_smoothPositivePart (s : ℝ) :
    HasDerivAt smoothPositivePart (Real.smoothTransition s) s :=
  intervalIntegral.integral_hasDerivAt_right
    (Real.smoothTransition.continuous.intervalIntegrable 0 s)
    Real.smoothTransition.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    Real.smoothTransition.continuous.continuousAt

theorem deriv_smoothPositivePart : deriv smoothPositivePart = Real.smoothTransition :=
  funext fun s ↦ (hasDerivAt_smoothPositivePart s).deriv

theorem contDiff_smoothPositivePart : ContDiff ℝ ∞ smoothPositivePart := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun s ↦ (hasDerivAt_smoothPositivePart s).differentiableAt,
    deriv_smoothPositivePart ▸ Real.smoothTransition.contDiff⟩

theorem smoothPositivePart_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    smoothPositivePart s = 0 := by
  rw [smoothPositivePart, intervalIntegral.integral_symm]
  have he : (∫ z in s..0, Real.smoothTransition z) = 0 := by
    rw [intervalIntegral.integral_of_le hs]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact Real.smoothTransition.zero_of_nonpos hz.2
  rw [he, neg_zero]

theorem smoothPositivePart_nonneg (s : ℝ) : 0 ≤ smoothPositivePart s := by
  rcases le_total s 0 with hs | hs
  · rw [smoothPositivePart_eq_zero_of_nonpos hs]
  · exact intervalIntegral.integral_nonneg hs (fun _ _ ↦ Real.smoothTransition.nonneg _)

theorem smoothPositivePart_le_posPart (s : ℝ) : smoothPositivePart s ≤ max s 0 := by
  rcases le_total s 0 with hs | hs
  · rw [smoothPositivePart_eq_zero_of_nonpos hs, max_eq_right hs]
  · rw [max_eq_left hs]
    have h := intervalIntegral.integral_mono_on (μ := volume) hs
      (Real.smoothTransition.continuous.intervalIntegrable 0 s)
      (continuous_const.intervalIntegrable 0 s)
      (fun z _ ↦ Real.smoothTransition.le_one z)
    simpa [smoothPositivePart] using h

theorem smoothPositivePart_pos {s : ℝ} (hs : 0 < s) : 0 < smoothPositivePart s := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (Real.smoothTransition.continuous.intervalIntegrable 0 s)
    (fun z hz ↦ Real.smoothTransition.pos_of_pos hz.1) hs

theorem smoothPositivePart_eq_zero_iff (s : ℝ) : smoothPositivePart s = 0 ↔ s ≤ 0 := by
  constructor
  · intro h
    by_contra hs
    exact (smoothPositivePart_pos (lt_of_not_ge hs)).ne' h
  · exact smoothPositivePart_eq_zero_of_nonpos

theorem deriv_smoothPositivePart_nonneg (s : ℝ) : 0 ≤ deriv smoothPositivePart s := by
  rw [deriv_smoothPositivePart]
  exact Real.smoothTransition.nonneg s

theorem deriv_deriv_smoothPositivePart_nonneg (s : ℝ) :
    0 ≤ deriv (deriv smoothPositivePart) s := by
  rw [deriv_smoothPositivePart]
  exact Real.smoothTransition.monotone.deriv_nonneg

end Poincare.Analysis.Heat

namespace PoincareConjecture.LeviCivitaData

open Poincare.Analysis.Heat


theorem smoothPositivePart_subsolution
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {u : ℝ × M → ℝ} {t : ℝ} (x : M)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ u (t, y)))
    (hut : DifferentiableAt ℝ (fun s ↦ u (s, x)) t)
    (hsub : deriv (fun s ↦ u (s, x)) t ≤ D.laplacian (fun y ↦ u (t, y)) x) :
    deriv (fun s ↦ smoothPositivePart (u (s, x))) t ≤
      D.laplacian (fun y ↦ smoothPositivePart (u (t, y))) x := by
  have hd := (hasDerivAt_smoothPositivePart (u (t, x))).comp t hut.hasDerivAt
  have hl := D.laplacian_comp hu contDiff_smoothPositivePart x
  simp only [Function.comp_def] at hd hl
  rw [hd.deriv, hl]
  have hm := mul_le_mul_of_nonneg_left hsub (Real.smoothTransition.nonneg (u (t, x)))
  have hg : 0 ≤ g.inner x (D.gradient (fun y ↦ u (t, y)) x)
      (D.gradient (fun y ↦ u (t, y)) x) := by
    by_cases hv : D.gradient (fun y ↦ u (t, y)) x = 0
    · simp [hv]
    · exact (g.pos x _ hv).le
  have hp := mul_nonneg (deriv_deriv_smoothPositivePart_nonneg (u (t, x))) hg
  rw [deriv_smoothPositivePart] at *
  linarith

end PoincareConjecture.LeviCivitaData
