import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.PeriodicBand

/-!
# Actual compact metric bounds for the angular flux

The conjugate form is bounded directly from its rotated metric-gradient
formula. Compactness of the closed annulus bounds the actual density and
inverse metric coefficients uniformly. The actual angular column of the
covering map has length `2*pi*r`. These facts yield a uniform bound for
the angular flux in terms of the actual differential norm.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

open Proofs.M58

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- The actual conjugate one-form has the expected coefficient bound in terms of the
density, inverse metric, and genuine differential. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-selection-flux.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarConjugateForm_norm_bound (H : Plane → ℝ) (x : Plane) :
    ‖scalarConjugateForm D H x‖ ≤
      (2 * |g.pullbackVolumeDensity id x| * ‖(g.euclideanCoefficients x).inverse‖) *
        ‖fderiv ℝ H x‖ := by
  let V : Plane := D.gradient H x
  have hproj (i : Fin 2) : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [one_mul, EuclideanSpace.coe_proj] using PiLp.norm_apply_le v i
  have hdf : mvfderiv (𝓡 2) H x = fderiv ℝ H x := by
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  have hgrad : ‖V‖ ≤
      ‖(g.euclideanCoefficients x).inverse‖ * ‖fderiv ℝ H x‖ := by
    dsimp only [V, LeviCivitaData.gradient]
    rw [hdf]
    exact (g.euclideanCoefficients x).inverse.le_opNorm _
  have hc (i : Fin 2) : |V i| ≤ ‖V‖ := PiLp.norm_apply_le V i
  have hrot : ‖scalarConjugateForm D H x‖ ≤
      2 * |g.pullbackVolumeDensity id x| * ‖V‖ := by
    unfold scalarConjugateForm M60.rotatedFlux
    calc
      _ ≤ ‖-(scalarMetricFlux D H 1 x) • EuclideanSpace.proj (0 : Fin 2)‖ +
          ‖scalarMetricFlux D H 0 x • EuclideanSpace.proj (1 : Fin 2)‖ := norm_add_le _ _
      _ ≤ |scalarMetricFlux D H 1 x| + |scalarMetricFlux D H 0 x| := by
        simp only [norm_smul, Real.norm_eq_abs, abs_neg]
        exact add_le_add ((mul_le_mul_of_nonneg_left (hproj 0) (abs_nonneg _)).trans_eq
          (mul_one _)) ((mul_le_mul_of_nonneg_left (hproj 1) (abs_nonneg _)).trans_eq
          (mul_one _))
      _ = |g.pullbackVolumeDensity id x| * |V 1| +
          |g.pullbackVolumeDensity id x| * |V 0| := by
        simp only [scalarMetricFlux, abs_mul]
        rfl
      _ ≤ |g.pullbackVolumeDensity id x| * ‖V‖ +
          |g.pullbackVolumeDensity id x| * ‖V‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hc 1) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hc 0) (abs_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ 2 * |g.pullbackVolumeDensity id x| * ‖V‖ := hrot
    _ ≤ 2 * |g.pullbackVolumeDensity id x| *
        (‖(g.euclideanCoefficients x).inverse‖ * ‖fderiv ℝ H x‖) :=
      mul_le_mul_of_nonneg_left hgrad (by positivity)
    _ = _ := by ring

/-- The angular column of the actual covering has its exact geometric length; this estimate
does not use any harmonicity of a potential. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-selection-flux.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarCoverMap_angular_norm (z : Cover) :
    ‖fderiv ℝ scalarCoverMap z (0, 1)‖ = |z.1| * (2 * Real.pi) := by
  have heq : fderiv ℝ scalarCoverMap z (0, 1) =
      (z.1 * (2 * Real.pi)) • angularPoint (2 * Real.pi * z.2 + Real.pi / 2) := by
    rw [scalarCoverMap_angular_column]
    ext i
    fin_cases i <;> simp [angularPoint, Real.cos_add, Real.sin_add] <;> ring
  rw [heq, norm_smul, Real.norm_eq_abs, abs_mul, norm_angularPoint, mul_one,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]

/-- Compact actual metric coefficients bound angular flux uniformly for every potential and
every point of the annular covering strip. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-boundary-selection-flux.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_scalarCover_angular_flux_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Plane → ℝ) (z : Cover), z ∈ scalarCoverStrip →
      |scalarCoverForm D H z (0, 1)| ≤ C * ‖fderiv ℝ H (scalarCoverMap z)‖ := by
  let B : Plane → ℝ := fun x =>
    2 * |g.pullbackVolumeDensity id x| * ‖(g.euclideanCoefficients x).inverse‖
  have hrho : Continuous (g.pullbackVolumeDensity id) :=
    continuous_iff_continuousAt.mpr fun x =>
      (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x) contMDiffAt_id
        (by simpa using Function.injective_id)).1.continuousAt
  have hIc : Continuous (fun x : Plane => (g.euclideanCoefficients x).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hi : (g.euclideanCoefficients x).IsInvertible := by
      convert! g.inner_isInvertible x
    exact (hi.contDiffAt_map_inverse.comp x (g.contDiffAt_euclideanCoefficients x)).continuousAt
  have hBc : Continuous B := by
    have hn : Continuous (fun A : (Plane →L[ℝ] ℝ) →L[ℝ] Plane => ‖A‖) := by
      convert! (continuous_norm (E := (Plane →L[ℝ] ℝ) →L[ℝ] Plane)) using 1
    exact (continuous_const.mul hrho.abs).mul (hn.comp hIc)
  obtain ⟨p, -, hmax⟩ := scalarClosedAnnulus_isCompact.exists_isMaxOn
    scalarClosedAnnulus_isConnected.nonempty hBc.continuousOn
  let K := max (B p) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨K * (4 * Real.pi), mul_pos hK (mul_pos (by norm_num) Real.pi_pos), ?_⟩
  intro H z hz
  have hx := scalarCoverMap_mem hz
  have hBx : B (scalarCoverMap z) ≤ K :=
    (hmax (((scalarAnnulusDefining_pos _).mpr hx).le)).trans (le_max_left _ _)
  have hform : ‖scalarConjugateForm D H (scalarCoverMap z)‖ ≤
      K * ‖fderiv ℝ H (scalarCoverMap z)‖ :=
    (scalarConjugateForm_norm_bound D H _).trans
      (mul_le_mul_of_nonneg_right hBx (norm_nonneg _))
  have hcol : ‖fderiv ℝ scalarCoverMap z (0, 1)‖ ≤ 4 * Real.pi := by
    rw [scalarCoverMap_angular_norm, abs_of_pos (zero_lt_one.trans hz.1)]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hz.2.le Real.pi_pos.le]
  calc
    _ ≤ ‖scalarConjugateForm D H (scalarCoverMap z)‖ *
        ‖fderiv ℝ scalarCoverMap z (0, 1)‖ :=
      (scalarConjugateForm D H (scalarCoverMap z)).le_opNorm _
    _ ≤ (K * ‖fderiv ℝ H (scalarCoverMap z)‖) * (4 * Real.pi) :=
      mul_le_mul hform hcol (norm_nonneg _) (mul_nonneg hK.le (norm_nonneg _))
    _ = _ := by ring

end PoincareMT.M64Uniformization
