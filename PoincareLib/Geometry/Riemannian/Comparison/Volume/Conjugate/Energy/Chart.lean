import PoincareLib.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Length
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients

/-!
# Coordinate energy and intrinsic speed

The energy used by the coordinate second-variation formula is the squared
intrinsic speed of the corresponding manifold path. This identification feeds
the minimizing-segment energy lower bound.

Reference: Morgan--Tian, Theorem 1.34, p. 19.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The speed of a coordinate path is the square root of its metric energy density. -/
theorem tangentNorm_comp_eq_sqrt_pullback
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {u : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f (u t)) (hu : DifferentiableAt ℝ u t) :
    g.tangentNorm (f (u t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ u) t 1) =
      Real.sqrt (g.pullbackCoefficients f (u t) (deriv u t) (deriv u t)) := by
  have hd := mfderiv_comp t hf hu.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hd
  have hd1 := congrArg (fun L => L 1) hd
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ u) t 1 =
    mfderiv (𝓡 n) (𝓡 n) f (u t) (fderiv ℝ u t 1) at hd1
  rw [fderiv_eq_smul_deriv, one_smul] at hd1
  rw [hd1]
  rfl

/-- Squared intrinsic speed equals coordinate metric energy density. -/
theorem tangentNorm_comp_sq_eq_pullback
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {u : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f (u t)) (hu : DifferentiableAt ℝ u t) :
    (g.tangentNorm (f (u t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ u) t 1)) ^ 2 =
      g.pullbackCoefficients f (u t) (deriv u t) (deriv u t) := by
  rw [g.tangentNorm_comp_eq_sqrt_pullback hf hu]
  apply Real.sq_sqrt
  change 0 ≤ g.inner (f (u t)) (mfderiv (𝓡 n) (𝓡 n) f (u t) (deriv u t))
    (mfderiv (𝓡 n) (𝓡 n) f (u t) (deriv u t))
  by_cases hv : mfderiv (𝓡 n) (𝓡 n) f (u t) (deriv u t) = 0
  · simp [hv]
  · exact (g.pos _ _ hv).le

/-- Smooth coordinate curves have continuous intrinsic speed on chart intervals. -/
theorem continuousOn_speed_chart_comp
    (g : RiemannianMetric n M) (p : M)
    {u : ℝ → EuclideanSpace ℝ (Fin n)} {S : Set ℝ}
    (hu : ∀ t ∈ S, ContDiffAt ℝ 2 u t)
    (hmem : ∀ t ∈ S, u t ∈ (extChartAt (𝓡 n) p).target) :
    ContinuousOn (fun t => g.tangentNorm ((extChartAt (𝓡 n) p).symm (u t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) ((extChartAt (𝓡 n) p).symm ∘ u) t 1)) S := by
  let f := (extChartAt (𝓡 n) p).symm
  have hf (t : ℝ) (ht : t ∈ S) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (u t) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (hmem t ht))
  apply ContinuousOn.congr (f := fun t =>
    Real.sqrt (g.pullbackCoefficients f (u t) (deriv u t) (deriv u t)))
  · intro t ht
    have hB : ContDiffAt ℝ 1 (fun s => g.pullbackCoefficients f (u s)) t :=
      ((g.contDiffAt_pullbackCoefficients (hf t ht)).of_le (by simp)).comp t
        ((hu t ht).of_le (by norm_num))
    have hd : ContDiffAt ℝ 1 (deriv u) t :=
      ((hu t ht).fderiv_right (by norm_num)).clm_apply contDiffAt_const
    exact (((hB.clm_apply hd).clm_apply hd).continuousAt.sqrt).continuousWithinAt
  · intro t ht
    exact g.tangentNorm_comp_eq_sqrt_pullback ((hf t ht).mdifferentiableAt (by simp))
      ((hu t ht).differentiableAt (by simp))

end PoincareMT.RiemannianMetric
