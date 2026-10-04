import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.Round.Metric
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Functionals
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The regularized pullback metric for area-to-energy approximation

Morgan-Tian Lemma 18.10, printed pp. 424-426, with the area-to-energy
correction in `reviews/errata/2026-09-14-sphere-area.md`. Adding a positive
multiple of the actual round metric to the actual pullback form gives a
smooth metric even where the sphere map has deficient rank.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

noncomputable section

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance regularizedTangentNormedAddCommGroup (p : UnitTwoSphere) :
    NormedAddCommGroup (TangentSpace (𝓡 2) p) :=
  inferInstanceAs (NormedAddCommGroup LoopPlane)

local instance regularizedTangentNormedSpace (p : UnitTwoSphere) :
    NormedSpace ℝ (TangentSpace (𝓡 2) p) :=
  inferInstanceAs (NormedSpace ℝ LoopPlane)

local instance regularizedCotangentContinuousAdd :
    ∀ p : UnitTwoSphere, ContinuousAdd (TangentSpace (𝓡 2) p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (LoopPlane →L[ℝ] ℝ))

private theorem pullback_nonneg (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) (v : TangentSpace (𝓡 2) p) :
    0 ≤ M60.metricPullbackForm (n := 2) g f p v v := by
  change 0 ≤ g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
    (mfderiv (𝓡 2) (𝓡 n) f p v)
  by_cases hv : mfderiv (𝓡 2) (𝓡 n) f p v = 0
  · simp [hv]
  · exact (g.pos _ _ hv).le

/-- The positive regularization of the actual possibly degenerate pullback.
Source: MT Lemma 18.10, pp. 424-426, area-to-energy erratum. -/
noncomputable def m60SphereRegularizedMetric (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) : RiemannianMetric 2 UnitTwoSphere where
  inner p := M60.metricPullbackForm (n := 2) g f p + delta • m60RoundSphereMetric.inner p
  symm p v w := by
    change g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p w) +
        delta * m60RoundSphereMetric.inner p v w = _
    rw [g.symm, m60RoundSphereMetric.symm]
    rfl
  pos p v hv := add_pos_of_nonneg_of_pos (pullback_nonneg g f p v)
    (mul_pos hdelta (m60RoundSphereMetric.pos p v hv))
  isVonNBounded p := by
    let L : TangentSpace (𝓡 2) p →L[ℝ] TangentSpace (𝓡 2) p :=
      (Real.sqrt delta)⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) p)
    refine ((m60RoundSphereMetric.isVonNBounded p).image L).subset ?_
    intro v hv
    refine ⟨Real.sqrt delta • v, ?_, ?_⟩
    · change m60RoundSphereMetric.inner p (Real.sqrt delta • v)
        (Real.sqrt delta • v) < 1
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, Real.mul_self_sqrt hdelta.le]
      have h := pullback_nonneg g f p v
      change M60.metricPullbackForm (n := 2) g f p v v +
        delta * m60RoundSphereMetric.inner p v v < 1 at hv
      linarith
    · change (Real.sqrt delta)⁻¹ • (Real.sqrt delta • v) = v
      rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hdelta), one_smul]
  contMDiff p := (M60.metricPullbackForm_contMDiffAt g (hf p)).add_section
    ((m60RoundSphereMetric.contMDiff p).const_smul_section (a := delta))

/-- The regularization is exactly the actual pullback plus delta times
the frozen round inner form. Source: MT Lemma 18.10, pp. 424-426, erratum. -/
theorem m60SphereRegularizedMetric_inner (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (p : UnitTwoSphere)
    (v w : TangentSpace (𝓡 2) p) :
    (m60SphereRegularizedMetric g f hf delta hdelta).inner p v w =
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p w) +
      delta * m60RoundSphereInner p v w := rfl

/-- The regularized metric dominates the actual pullback quadratic form.
Source: MT Lemma 18.10, pp. 424-426, area-to-energy erratum. -/
theorem m60SphereRegularizedMetric_dominates (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (p : UnitTwoSphere)
    (v : TangentSpace (𝓡 2) p) :
    g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v) ≤
      (m60SphereRegularizedMetric g f hf delta hdelta).inner p v v := by
  rw [m60SphereRegularizedMetric_inner]
  have hr : 0 ≤ m60RoundSphereInner p v v := by
    by_cases hv : v = 0
    · simp [hv, m60RoundSphereInner]
    · exact (m60RoundSphereMetric.pos p v hv).le
  exact le_add_of_nonneg_right (mul_nonneg hdelta.le hr)

end PoincareMT

end
