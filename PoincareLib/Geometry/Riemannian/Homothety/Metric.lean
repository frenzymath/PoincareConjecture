import PoincareLib.Geometry.Riemannian.Homothety.Basic
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M13/Metric.lean`,
revision `0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See `references/ricci-flow/mapher/rescaling-import.json`. -/

/-!
# Positive scaling of smooth metrics

The scaled metric uses the original vector bundle and its topology. Its unit
ball is bounded by rescaling the original unit ball by the inverse square
root. These constructions implement the metric factor in Morgan-Tian
Definition 3.40, p. 61, with the norm convention of Definition 1.1, pp. 3-4.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.Homothety

section Bundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (Bundle.TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- Constant positive scaling on the same smooth vector bundle. -/
noncomputable def scaleSmoothMetric (g : Bundle.ContMDiffRiemannianMetric IB ∞ F E)
    (Q : ℝ) (hQ : 0 < Q) : Bundle.ContMDiffRiemannianMetric IB ∞ F E where
  inner b := Q • g.inner b
  symm b v w := congrArg (Q * ·) (g.symm b v w)
  pos b v hv := mul_pos hQ (g.pos b v hv)
  isVonNBounded b := by
    let c := Real.sqrt Q
    have hc : c ≠ 0 := (Real.sqrt_pos.2 hQ).ne'
    have hc2 : c * c = Q := Real.mul_self_sqrt hQ.le
    apply Bornology.IsVonNBounded.subset ?_
      ((g.isVonNBounded b).image (c⁻¹ • ContinuousLinearMap.id ℝ (E b)))
    intro v hv
    refine ⟨c • v, ?_, ?_⟩
    · change g.inner b (c • v) (c • v) < 1
      change Q * g.inner b v v < 1 at hv
      simpa only [map_smul, smul_apply, smul_eq_mul, ← mul_assoc, hc2] using hv
    · change c⁻¹ • (c • v) = v
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  contMDiff := g.contMDiff.const_smul_section

/-- The bilinear form is multiplied by the prescribed positive constant. -/
theorem scaleSmoothMetric_inner (g : Bundle.ContMDiffRiemannianMetric IB ∞ F E)
    (Q : ℝ) (hQ : 0 < Q) (b : B) (v w : E b) :
    (scaleSmoothMetric g Q hQ).inner b v w = Q * g.inner b v w := rfl

end Bundle

section Tangent

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]

/-- Every metric homothety has the square-root tangent norm factor. -/
theorem homothety_tangentNorm (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (x : M) (v : TangentSpace (𝓡 n) x) :
    h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) =
      Real.sqrt Q * g.tangentNorm x v := by
  unfold RiemannianMetric.tangentNorm
  rw [hf x v v, Real.sqrt_mul hQ.le]

/-- Squaring the norm gives the metric factor itself, including at zero. -/
theorem homothety_tangentNorm_sq (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (x : M) (v : TangentSpace (𝓡 n) x) :
    (h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)) ^ 2 =
      Q * (g.tangentNorm x v) ^ 2 := by
  rw [homothety_tangentNorm g h f Q hQ hf x v, mul_pow, Real.sq_sqrt hQ.le]

/-- The constructed metric realizes the expected norm on every tangent fiber. -/
theorem scaleSmoothMetric_tangentNorm (g : RiemannianMetric n M)
    (Q : ℝ) (hQ : 0 < Q) (x : M) (v : TangentSpace (𝓡 n) x) :
    RiemannianMetric.tangentNorm (scaleSmoothMetric g Q hQ) x v =
      Real.sqrt Q * g.tangentNorm x v := by
  unfold RiemannianMetric.tangentNorm
  rw [scaleSmoothMetric_inner, Real.sqrt_mul hQ.le]

end Tangent

end PoincareMT.Homothety
