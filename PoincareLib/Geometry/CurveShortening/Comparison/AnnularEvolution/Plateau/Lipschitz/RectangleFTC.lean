import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Rectangle.MeasurableIntegration
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Circle.PhaseEnergy
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Weak.LipschitzDerivatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Fundamental theorem on Lipschitz annular rectangles

Rademacher's theorem and Fubini identify the actual partial derivatives
on almost every slice. Absolute continuity then gives the boundary values.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

/-- The literal vertical annulus parametrization is one-Lipschitz. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusPoint_vertical_lipschitz (x : ℝ) :
    LipschitzWith 1 (annulusPoint x) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have heq : annulusPoint x a - annulusPoint x b =
      (a - b) • EuclideanSpace.single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  simp [dist_eq_norm, heq, norm_smul]

/-- The literal horizontal annulus parametrization is one-Lipschitz. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusPoint_horizontal_lipschitz (s : ℝ) :
    LipschitzWith 1 (fun x => annulusPoint x s) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have heq : annulusPoint a s - annulusPoint b s =
      (a - b) • EuclideanSpace.single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  simp [dist_eq_norm, heq, norm_smul]

/-- The actual scalar partial derivative of a Lipschitz annulus is integrable. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64_lipschitz_partial_integrable {f : LoopPlane → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain) (i : Fin 2) :
    IntegrableOn (fun p => fderiv ℝ f p (EuclideanSpace.single i 1)) S volume := by
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top⟩
  exact (memLp_top_fderiv_apply_of_lipschitzOn isOpen_interior
    (hf.mono interior_subset) (EuclideanSpace.single i 1)).integrable (by simp)

/-- Fubini and absolute continuity identify the actual vertical derivative integral with the
radial boundary difference. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem m64Annulus_integral_vertical_derivative_lipschitz
    {f : LoopPlane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    (∫ p in S, fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) =
      ∫ x in Icc (0 : ℝ) curvePeriod, f (annulusPoint x 1) - f (annulusPoint x 0) := by
  rw [m64AnnulusInteriorIntegral_eq_iterated_integrable _
    (m64_lipschitz_partial_integrable hf.lipschitzOnWith 1)]
  have hdiff := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (hf.ae_differentiableAt (μ := volume)))
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hdiff] with x hx
  have hslice : LipschitzWith (K * 1) (fun s => f (annulusPoint x s)) :=
    hf.comp (m64AnnulusPoint_vertical_lipschitz x)
  have hac := (hslice.lipschitzOnWith (s := uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
  calc
    _ = ∫ s in Icc (0 : ℝ) 1, deriv (fun t => f (annulusPoint x t)) s := by
      apply integral_congr_ae
      filter_upwards [hx] with s hs
      exact ((hs.hasFDerivAt.comp_hasDerivAt s
        (m64AnnulusPoint_vertical_hasDerivAt x s)).deriv).symm
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      exact hac.integral_deriv_eq_sub

/-- Fubini and absolute continuity identify the actual horizontal derivative integral with
the angular boundary difference. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem m64Annulus_integral_horizontal_derivative_lipschitz
    {f : LoopPlane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    (∫ p in S, fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) =
      ∫ s in Icc (0 : ℝ) 1,
        f (annulusPoint curvePeriod s) - f (annulusPoint 0 s) := by
  rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _
    (m64_lipschitz_partial_integrable hf.lipschitzOnWith 0)]
  have hdiff := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (hf.ae_differentiableAt (μ := volume)))
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hdiff
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with s hs
  have hslice : LipschitzWith (K * 1) (fun x => f (annulusPoint x s)) :=
    hf.comp (m64AnnulusPoint_horizontal_lipschitz s)
  have hac := (hslice.lipschitzOnWith
    (s := uIcc (0 : ℝ) curvePeriod)).absolutelyContinuousOnInterval
  calc
    _ = ∫ x in Icc (0 : ℝ) curvePeriod, deriv (fun t => f (annulusPoint t s)) x := by
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      exact ((hx.hasFDerivAt.comp_hasDerivAt x
        (m64AnnulusPoint_horizontal_hasDerivAt s x)).deriv).symm
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by unfold curvePeriod; positivity : 0 ≤ curvePeriod)]
      exact hac.integral_deriv_eq_sub

end PoincareMT
