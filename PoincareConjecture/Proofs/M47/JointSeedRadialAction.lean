import PoincareConjecture.Proofs.M47.JointSeedRadialClock
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M47



theorem jointSeed_radial_square_action_le
    (hM04 : RicciFlowCurvatureTheory.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (g : RiemannianMetric n M)
    (T d v K r : ℝ) (hd : 0 < d) (hv : 0 < v) (hvd : v < d)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hwindow : Icc (T - d) T ⊆ J)
    (gamma : ℝ → M) (hgamma : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma)
    {U : Set M} (hmap : MapsTo gamma (Icc (0 : ℝ) 1) U)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1, g.tangentNorm (gamma s) (curveVelocity (n := n) gamma s) ≤ r)
    (hupper : ∀ t ∈ Icc (T - d) (T - d + v), ∀ x ∈ U, ∀ w : TangentSpace (𝓡 n) x,
      (F.metric t).inner x w w ≤ g.inner x w w)
    (hscalar : ∀ t ∈ Icc (T - d) (T - d + v), ∀ x ∈ U,
      (F.connection t).scalarCurvature x ≤ K) :
    (∫ s in Real.sqrt (d - v)..Real.sqrt (d - v / 2),
      Proofs.M09.squareCurveActionDensity F T
        (fun z => gamma (2 * (z ^ 2 - (d - v)) / v)) s) ≤
      (K * v / 2 + 2 * r ^ 2 / v) * Real.sqrt d := by
  let beta (s : ℝ) := gamma (2 * (s ^ 2 - (d - v)) / v)
  let W := K + 4 * r ^ 2 / v ^ 2
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have htheta : 0 < d - v / 2 := by linarith
  have hstart : 0 < d - v := sub_pos.mpr hvd
  have hroots : Real.sqrt (d - v) ≤ Real.sqrt (d - v / 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsmallWindow : Icc (T - (d - v / 2)) T ⊆ J := by
    exact (Icc_subset_Icc (by linarith : T - d ≤ T - (d - v / 2)) le_rfl).trans hwindow
  have hbeta := jointSeed_radial_square_curve_smooth gamma hgamma d v
  have hfull := jointSeed_square_density_integrable (F := F) hM04 T (d - v / 2)
    htheta hsmallWindow beta isOpen_univ (subset_univ _) hbeta.contMDiffOn
  have hint : IntervalIntegrable (Proofs.M09.squareCurveActionDensity F T beta) volume
      (Real.sqrt (d - v)) (Real.sqrt (d - v / 2)) := hfull.mono_set (by
    rw [uIcc_of_le hroots, uIcc_of_le (Real.sqrt_nonneg _)]
    exact Icc_subset_Icc (Real.sqrt_nonneg _) le_rfl)
  have hlinear : IntervalIntegrable (fun s : ℝ => (2 * W * Real.sqrt d) * s) volume
      (Real.sqrt (d - v)) (Real.sqrt (d - v / 2)) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hcomparison := intervalIntegral.integral_mono_on hroots hint hlinear (fun s hs => by
    obtain ⟨hspos, hslo, hshi, hparameter⟩ := jointSeed_radial_parameter_bounds hv hvd hs
    have htime : T - s ^ 2 ∈ Icc (T - d) (T - d + v) :=
      ⟨by linarith, by linarith⟩
    have hx : beta s ∈ U := hmap hparameter
    have hR := hscalar (T - s ^ 2) htime (beta s) hx
    have hreference := jointSeed_radial_square_reference_energy g gamma hgamma hr
      (hspeed _ hparameter)
    have henergy : (F.metric (T - s ^ 2)).inner (beta s)
        (curveVelocity (n := n) beta s) (curveVelocity (n := n) beta s) ≤ (4 * s / v) ^ 2 * r ^ 2 :=
      (hupper (T - s ^ 2) htime (beta s) hx _).trans hreference
    have hdensity : Proofs.M09.squareCurveActionDensity F T beta s ≤ 2 * s ^ 2 * W := by
      change 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (beta s) +
        (1 / 2 : ℝ) * (F.metric (T - s ^ 2)).inner (beta s)
          (curveVelocity (n := n) beta s) (curveVelocity (n := n) beta s) ≤ _
      calc
        _ ≤ 2 * s ^ 2 * K + (1 / 2 : ℝ) * ((4 * s / v) ^ 2 * r ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hR (by positivity))
            (mul_le_mul_of_nonneg_left henergy (by norm_num))
        _ = _ := by dsimp only [W]; field_simp; ring
    have hroot : s ≤ Real.sqrt d := hs.2.trans (Real.sqrt_le_sqrt (by linarith))
    have hmul := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 2 * W * s)
    nlinarith)
  have hvalue : (∫ s in Real.sqrt (d - v)..Real.sqrt (d - v / 2),
      (2 * W * Real.sqrt d) * s) = (K * v / 2 + 2 * r ^ 2 / v) * Real.sqrt d := by
    rw [intervalIntegral.integral_const_mul, integral_id,
      Real.sq_sqrt htheta.le, Real.sq_sqrt hstart.le]
    dsimp only [W]
    field_simp
    ring
  exact hcomparison.trans_eq hvalue

end PoincareConjecture.M47
