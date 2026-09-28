import PoincareConjecture.Definitions.M62Curve
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem curvatureSquared_nonneg (t x : ℝ) : 0 ≤ m62CurvatureSquared F c t x := by
  exact ((F.metric t).toRiemannianMetric.toCore (c x t)).re_inner_nonneg _

theorem curvature_nonneg (t x : ℝ) : 0 ≤ m62Curvature F c t x :=
  Real.sqrt_nonneg _

theorem curvature_sq (t x : ℝ) :
    m62Curvature F c t x ^ 2 = m62CurvatureSquared F c t x :=
  Real.sq_sqrt (curvatureSquared_nonneg F c t x)

theorem regularized_radicand_pos {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    0 < m62CurvatureSquared F c t x + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (curvatureSquared_nonneg F c t x) (sq_pos_of_pos hε)

theorem regularized_pos {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    0 < m62RegularizedCurvature F c ε t x :=
  Real.sqrt_pos.mpr (regularized_radicand_pos F c hε t x)

theorem regularized_sq (ε t x : ℝ) :
    m62RegularizedCurvature F c ε t x ^ 2 = m62CurvatureSquared F c t x + ε ^ 2 :=
  Real.sq_sqrt (add_nonneg (curvatureSquared_nonneg F c t x) (sq_nonneg ε))

theorem curvature_le_regularized (ε t x : ℝ) :
    m62Curvature F c t x ≤ m62RegularizedCurvature F c ε t x :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))

theorem curvature_lt_regularized {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    m62Curvature F c t x < m62RegularizedCurvature F c ε t x :=
  Real.sqrt_lt_sqrt (curvatureSquared_nonneg F c t x)
    (lt_add_of_pos_right _ (sq_pos_of_pos hε))

theorem regularized_sub_curvature_le {ε : ℝ} (hε : 0 ≤ ε) (t x : ℝ) :
    m62RegularizedCurvature F c ε t x - m62Curvature F c t x ≤ ε := by
  have hk := curvature_nonneg F c t x
  have hk2 := curvature_sq F c t x
  have hupper : m62RegularizedCurvature F c ε t x ≤ m62Curvature F c t x + ε := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨add_nonneg hk hε, by nlinarith [mul_nonneg hk hε]⟩
  linarith

theorem regularized_smooth {ε : ℝ} (hε : 0 < ε)
    (hq : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ m62CurvatureSquared F c z.2 z.1)
      (Set.univ ×ˢ Set.Ioo a b)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ m62RegularizedCurvature F c ε z.2 z.1)
      (Set.univ ×ˢ Set.Ioo a b) := by
  exact (hq.add contDiffOn_const).sqrt
    (fun z _ ↦ (regularized_radicand_pos F c hε z.2 z.1).ne')

theorem regularized_hasDerivAt_time {ε t x q' : ℝ} (hε : 0 < ε)
    (hq : HasDerivAt (fun s ↦ m62CurvatureSquared F c s x) q' t) :
    HasDerivAt (fun s ↦ m62RegularizedCurvature F c ε s x)
      (q' / (2 * m62RegularizedCurvature F c ε t x)) t := by
  exact (hq.add_const (ε ^ 2)).sqrt (regularized_radicand_pos F c hε t x).ne'

theorem regularized_hasDerivAt_parameter {ε t x q' : ℝ} (hε : 0 < ε)
    (hq : HasDerivAt (m62CurvatureSquared F c t) q' x) :
    HasDerivAt (m62RegularizedCurvature F c ε t)
      (q' / (2 * m62RegularizedCurvature F c ε t x)) x := by
  exact (hq.add_const (ε ^ 2)).sqrt (regularized_radicand_pos F c hε t x).ne'

end PoincareConjecture.M62
