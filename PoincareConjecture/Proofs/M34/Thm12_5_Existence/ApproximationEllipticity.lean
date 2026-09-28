import PoincareConjecture.Proofs.M34.Thm12_5_Existence.ApproximationCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.Perturbation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34.CompactCapApproximation

variable {g0 : StandardInitialMetric} (A : CompactCapApproximation g0)

theorem coefficients_exp_bounds (P : RicciFlowCurvatureTheory.{0})
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) (v : StandardCapSpace) :
    Real.exp (-6 * A.curvature_bound 0 * t) * g0.metric.euclideanCoefficients x v v ≤
        A.coefficients k t x v v ∧
      A.coefficients k t x v v ≤
        Real.exp (6 * A.curvature_bound 0 * t) * g0.metric.euclideanCoefficients x v v := by
  have h := P.metric_comparison 3 (CompactCapDouble g0 k) (Icc 0 A.time)
    (A.flow k) 0 t (A.curvature_bound 0) ⟨le_rfl, A.time_pos.le⟩ ht ht.1
    (A.bound_pos 0).le (fun s hs q => A.full_curvature_le k ⟨hs.1, hs.2.trans ht.2⟩ q)
    (compactCapChart g0 k x) (mfderiv (𝓡 3) (𝓡 3) (compactCapChart g0 k) x v)
  change Real.exp (-2 * (3 : ℝ) * A.curvature_bound 0 * (t - 0)) *
      A.coefficients k 0 x v v ≤ A.coefficients k t x v v ∧
    A.coefficients k t x v v ≤
      Real.exp (2 * (3 : ℝ) * A.curvature_bound 0 * (t - 0)) *
        A.coefficients k 0 x v v at h
  rw [A.coefficients_zero k hx] at h
  norm_num at h ⊢
  exact h

theorem exists_compact_ellipticity (P : RicciFlowCurvatureTheory.{0})
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ k t, t ∈ Icc 0 A.time →
      ∀ x ∈ K, x ∈ compactCapSource g0 k → ∀ v : StandardCapSpace,
        a * ‖v‖ ^ 2 ≤ A.coefficients k t x v v ∧
          A.coefficients k t x v v ≤ b * ‖v‖ ^ 2 := by
  have hcont : ContinuousOn g0.metric.euclideanCoefficients K :=
    fun x _ => (g0.metric.contDiffAt_euclideanCoefficients x).continuousAt.continuousWithinAt
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hcont
    (fun x _ v hv => g0.metric.pos x v hv)
  have hnorm : ∃ b : ℝ, ∀ x ∈ K, ‖g0.metric.euclideanCoefficients x‖ ≤ b :=
    hK.exists_bound_of_continuousOn (f := g0.metric.euclideanCoefficients) hcont
  obtain ⟨b, hb⟩ := hnorm
  have hupper (x : StandardCapSpace) (hx : x ∈ K) (v : StandardCapSpace) :
      g0.metric.euclideanCoefficients x v v ≤ max b 0 * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖g0.metric.euclideanCoefficients x v v‖ := le_abs_self _
      _ ≤ ‖g0.metric.euclideanCoefficients x‖ * ‖v‖ * ‖v‖ :=
        (g0.metric.euclideanCoefficients x).le_opNorm₂ v v
      _ = ‖g0.metric.euclideanCoefficients x‖ * ‖v‖ ^ 2 := by ring
      _ ≤ max b 0 * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right ((hb x hx).trans (le_max_left _ _)) (sq_nonneg _)
  refine ⟨Real.exp (-6 * A.curvature_bound 0 * A.time) * a,
    Real.exp (6 * A.curvature_bound 0 * A.time) * max b 0,
    mul_pos (Real.exp_pos _) ha, by positivity, ?_⟩
  intro k t ht x hx hsource v
  have hnonneg : 0 ≤ g0.metric.euclideanCoefficients x v v :=
    (mul_nonneg ha.le (sq_nonneg _)).trans (hlower x hx v)
  have hcomparison := A.coefficients_exp_bounds P k ht hsource v
  have htime := mul_le_mul_of_nonneg_left ht.2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (A.bound_pos 0).le)
  constructor
  · calc
      _ = Real.exp (-6 * A.curvature_bound 0 * A.time) * (a * ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-6 * A.curvature_bound 0 * A.time) *
          g0.metric.euclideanCoefficients x v v :=
        mul_le_mul_of_nonneg_left (hlower x hx v) (Real.exp_pos _).le
      _ ≤ Real.exp (-6 * A.curvature_bound 0 * t) *
          g0.metric.euclideanCoefficients x v v :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hnonneg
      _ ≤ _ := hcomparison.1
  · calc
      _ ≤ Real.exp (6 * A.curvature_bound 0 * t) *
          g0.metric.euclideanCoefficients x v v := hcomparison.2
      _ ≤ Real.exp (6 * A.curvature_bound 0 * A.time) *
          g0.metric.euclideanCoefficients x v v :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htime) hnonneg
      _ ≤ Real.exp (6 * A.curvature_bound 0 * A.time) * (max b 0 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hupper x hx v) (Real.exp_pos _).le
      _ = _ := by ring

theorem norm_coefficients_le (k : ℕ) (t : ℝ) (x : StandardCapSpace)
    {b : ℝ} (hb : 0 ≤ b) (hupper : ∀ v, A.coefficients k t x v v ≤ b * ‖v‖ ^ 2) :
    ‖A.coefficients k t x‖ ≤ b := by
  apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
  · intro u v
    exact ((A.flow k).metric t).symm _ _ _
  · intro v
    have hn : 0 ≤ A.coefficients k t x v v := by
      let w := mfderiv (𝓡 3) (𝓡 3) (compactCapChart g0 k) x v
      change 0 ≤ ((A.flow k).metric t).inner (compactCapChart g0 k x) w w
      by_cases hw : w = 0
      · simp [hw]
      · exact (((A.flow k).metric t).pos _ _ hw).le
    rw [abs_of_nonneg hn]
    exact hupper v

end PoincareConjecture.M34.CompactCapApproximation
