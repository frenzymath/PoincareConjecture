import PoincareConjecture.Proofs.M47.JointSeedSquarePath
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J}



theorem jointSeed_constant_square_density (T s : ℝ) (q : M) :
    Proofs.M09.squareCurveActionDensity F T (fun _ => q) s =
      2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature q := by
  simp only [Proofs.M09.squareCurveActionDensity, Proofs.M09.regularizedCurveEnergy,
    curveVelocity, mfderiv_const, zero_apply, map_zero, mul_zero, add_zero]



theorem jointSeed_constant_square_action_le
    (hM04 : RicciFlowCurvatureTheory.{u}) (T d v K : ℝ) (q : M)
    (hd : 0 < d) (hv : 0 < v) (hvd : v < d) (hK : 0 ≤ K)
    (hwindow : Icc (T - d) T ⊆ J)
    (hscalar : ∀ t ∈ Icc (T - d) (T - d + v),
      (F.connection t).scalarCurvature q ≤ K) :
    (∫ s in Real.sqrt (d - v)..Real.sqrt d,
      Proofs.M09.squareCurveActionDensity F T (fun _ => q) s) ≤ K * v * Real.sqrt d := by
  have htheta : 0 < d - v := sub_pos.mpr hvd
  have hroots : Real.sqrt (d - v) ≤ Real.sqrt d := Real.sqrt_le_sqrt (by linarith)
  have hfull := jointSeed_square_density_integrable (F := F) hM04 T d hd hwindow
    (fun _ => q) isOpen_univ (subset_univ _) contMDiffOn_const
  have hi : IntervalIntegrable (Proofs.M09.squareCurveActionDensity F T (fun _ => q))
      volume (Real.sqrt (d - v)) (Real.sqrt d) := hfull.mono_set (by
    rw [uIcc_of_le hroots, uIcc_of_le (Real.sqrt_nonneg d)]
    exact Icc_subset_Icc (Real.sqrt_nonneg _) le_rfl)
  have hj : IntervalIntegrable (fun s : ℝ => (2 * K * Real.sqrt d) * s)
      volume (Real.sqrt (d - v)) (Real.sqrt d) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hcompare := intervalIntegral.integral_mono_on hroots hi hj (fun s hs => by
    have hspos : 0 ≤ s := (Real.sqrt_nonneg (d - v)).trans hs.1
    have hslo : d - v ≤ s ^ 2 := by
      simpa only [Real.sq_sqrt htheta.le] using
        (sq_le_sq₀ (Real.sqrt_nonneg (d - v)) hspos).2 hs.1
    have hshi : s ^ 2 ≤ d := by
      simpa only [Real.sq_sqrt hd.le] using
        (sq_le_sq₀ hspos (Real.sqrt_nonneg d)).2 hs.2
    have hR := hscalar (T - s ^ 2) ⟨by linarith, by linarith⟩
    rw [jointSeed_constant_square_density]
    have hfirst := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2 * s ^ 2)
    have hsecond := mul_le_mul_of_nonneg_left hs.2
      (by positivity : 0 ≤ 2 * K * s)
    nlinarith)
  have hvalue : (∫ s in Real.sqrt (d - v)..Real.sqrt d, (2 * K * Real.sqrt d) * s) =
      K * v * Real.sqrt d := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    rw [Real.sq_sqrt hd.le, Real.sq_sqrt htheta.le]
    ring
  exact hcompare.trans_eq hvalue



theorem jointSeed_birth_action_normalization {d A L v : ℝ}
    (hd : 0 < d) (hA : 0 < A) (hbudget : A * L * v ≤ 1 / 4) :
    (3 * Real.sqrt d + (4 * L / 3) * v * Real.sqrt d) / (2 * Real.sqrt d) ≤
      3 / 2 + 1 / (6 * A) := by
  have hroot : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hvalue : (3 * Real.sqrt d + (4 * L / 3) * v * Real.sqrt d) /
      (2 * Real.sqrt d) = 3 / 2 + 2 * L * v / 3 := by
    field_simp
    ring
  rw [hvalue]
  rw [add_le_add_iff_left]
  apply (le_div_iff₀ (by positivity : 0 < 6 * A)).2
  nlinarith

end PoincareConjecture.M47
