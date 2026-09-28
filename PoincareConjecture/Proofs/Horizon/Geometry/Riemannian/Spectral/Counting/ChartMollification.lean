import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Localization
import PoincareConjecture.Proofs.Horizon.Analysis.Spectral.Counting.Mollification
import PoincareConjecture.Proofs.Horizon.Analysis.Spectral.Counting.MollifierTrace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Spectral.Counting.ChartLocalization

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff Convolution

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Counting

open Poincare.Analysis.Sobolev Poincare.Analysis.Spectral.Counting

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

private theorem norm_sub_sq_eq_integral_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : Lp ℝ 2 μ}
    {f h : α → ℝ} (ha : ⇑a =ᵐ[μ] f) (hb : ⇑b =ᵐ[μ] h) :
    ‖a - b‖ ^ 2 = ∫ x, (f x - h x) ^ 2 ∂μ := by
  rw [Lp.norm_def, eLpNorm_toReal_sq_eq_integral (Lp.memLp (a - b))]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub a b, ha, hb] with x hsub hax hbx
  simp only [hsub, Pi.sub_apply, hax, hbx]

theorem exists_integral_chart_mollification_sub_sq_le_energy
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ e.target) :
    ∃ B ≥ 0, ∀ (f : EnergyTest D Ω) {ε : ℝ} (hε : 0 < ε),
      (∫ x : EuclideanSpace ℝ (Fin n),
        ((mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          chartPullback e (f.mulSmooth χ hχ)) x -
            chartPullback e (f.mulSmooth χ hχ) x) ^ 2) ≤
        B * ε ^ 2 * ‖f‖ ^ 2 := by
  obtain ⟨A, hA, hder⟩ := exists_integral_chart_fderiv_sq_le_energy
    (D := D) (Ω := Ω) e he hei hcχ hsχ
  obtain ⟨C, hC, hmul⟩ := exists_mulSmooth_norm_bound (D := D) (Ω := Ω) χ hχ hcχ
  refine ⟨A * C ^ 2, mul_nonneg hA (sq_nonneg C), fun f ε hε => ?_⟩
  have hs := (f.mulSmooth_support_subset χ hχ).trans hsχ
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (hmul f) 2
  have hchart := integral_mollifierEps_convolution_sub_sq_le hε
    ((contDiff_chartPullback e he (f.mulSmooth χ hχ).smooth
      (f.mulSmooth χ hχ).hasCompactSupport hs).of_le (by simp))
    (hasCompactSupport_chartPullback e (f.mulSmooth χ hχ).hasCompactSupport hs)
  calc
    _ ≤ ε ^ 2 * ∫ x, ‖fderiv ℝ (chartPullback e (f.mulSmooth χ hχ)) x‖ ^ 2 := hchart
    _ ≤ ε ^ 2 * (A * ‖f.mulSmooth χ hχ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hder _ (f.mulSmooth_support_subset χ hχ)) (sq_nonneg ε)
    _ ≤ ε ^ 2 * (A * (C * ‖f‖) ^ 2) := by gcongr
    _ = A * C ^ 2 * ε ^ 2 * ‖f‖ ^ 2 := by ring

theorem exists_norm_chartLocalization_sub_mollifyOn_sq_le_energy
    (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ e.target) :
    ∃ B ≥ 0, ∀ (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1) (u : H1Zero D Ω),
      let S := Metric.cthickening 1 (e.symm '' tsupport χ)
      let L := chartLocalization D Ω hΩ hcΩ e he hei χ hχ hcχ hsχ
      ‖L (toDomainL2 D Ω u) -
        mollifyOn S Metric.isClosed_cthickening.measurableSet
          ((hcχ.image_of_continuousOn (e.symm.continuousOn.mono hsχ)).cthickening).measure_ne_top
          hε (L (toDomainL2 D Ω u))‖ ^ 2 ≤ B * ε ^ 2 * ‖u‖ ^ 2 := by
  obtain ⟨B, hB, htest⟩ := exists_integral_chart_mollification_sub_sq_le_energy
    (D := D) (Ω := Ω) e he hei χ hχ hcχ hsχ
  refine ⟨B, hB, fun ε hε hε1 u => ?_⟩
  let S := Metric.cthickening 1 (e.symm '' tsupport χ)
  have hS : MeasurableSet S := Metric.isClosed_cthickening.measurableSet
  have hSvol : volume S ≠ ⊤ :=
    ((hcχ.image_of_continuousOn (e.symm.continuousOn.mono hsχ)).cthickening).measure_ne_top
  let L := (chartLocalization D Ω hΩ hcΩ e he hei χ hχ hcχ hsχ).comp (toDomainL2 D Ω)
  let A := mollifyOn S hS hSvol hε
  change ‖L u - A (L u)‖ ^ 2 ≤ B * ε ^ 2 * ‖u‖ ^ 2
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_le ((L.continuous.sub (A.continuous.comp L.continuous)).norm.pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  | ih f =>
    have hf := (f.mulSmooth χ hχ).chartPullback_memLp e he
      ((f.mulSmooth_support_subset χ hχ).trans hsχ)
    have hL : L (f : H1Zero D Ω) = hf.toLp _ :=
      chartLocalization_test hΩ hcΩ e he hei χ hχ hcχ hsχ f
    rw [hL, Completion.norm_coe, norm_sub_rev]
    have hm := mollifyOn_toLp_coeFn S hS hSvol hε hf
    have hs : tsupport (chartPullback e (f.mulSmooth χ hχ)) ⊆ e.symm '' tsupport χ :=
      (tsupport_chartPullback_subset_image e (f.mulSmooth χ hχ).hasCompactSupport
        ((f.mulSmooth_support_subset χ hχ).trans hsχ)).trans
          (image_mono (f.mulSmooth_support_subset χ hχ))
    have hind := indicator_cthickening_mollifierEps_convolution hε hε1 hs
    change S.indicator _ = _ at hind
    rw [hind] at hm
    rw [norm_sub_sq_eq_integral_of_ae hm hf.coeFn_toLp]
    exact htest f hε

end PoincareConjecture.LeviCivitaData.Dirichlet.Counting
