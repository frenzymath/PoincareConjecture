import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderPullback
import PoincareConjecture.Proofs.M34.Mathlib.NeckChartDerivative











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem capPersistence_chart_pullback (g : RiemannianMetric n M) (a : M)
    {φ : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hφ : MDifferentiableAt (𝓡 n) (𝓡 n) φ x)
    (ha : φ x ∈ (extChartAt (𝓡 n) a).source) :
    (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm
      ((extChartAt (𝓡 n) a) (φ x))).bilinearComp (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ φ) x)
          (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ φ) x) = g.pullbackCoefficients φ x := by
  have hd := mfderiv_inverse_chart_comp_fderiv_coordinates a hφ ha
  ext v w
  change g.inner _
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm ((extChartAt (𝓡 n) a) (φ x))
      (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ φ) x v))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm ((extChartAt (𝓡 n) a) (φ x))
      (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ φ) x w)) =
    g.inner (φ x) (mfderiv (𝓡 n) (𝓡 n) φ x v) (mfderiv (𝓡 n) (𝓡 n) φ x w)
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  exact (congrArg₂ (fun V W : EuclideanSpace ℝ (Fin n) =>
    g.inner ((extChartAt (𝓡 n) a).symm ((extChartAt (𝓡 n) a) (φ x))) V W) hv hw).trans
      (congrArg (fun y : M => g.inner y (mfderiv (𝓡 n) (𝓡 n) φ x v)
        (mfderiv (𝓡 n) (𝓡 n) φ x w)) ((extChartAt (𝓡 n) a).left_inv ha))

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.EpsilonNeck

open M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)




theorem capPersistenceEuclideanMap_origin_lower (q : UnitTwoSphere) (s : ℝ)
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : E₃) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ N.scale⁻¹ ^ 2 *
      g.pullbackCoefficients (N.capPersistenceEuclideanMap q s) 0 v v := by
  have hx : (0 : E₃) 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by simpa using hs
  have hc := (N.pullback_inner_comparison (z := capPersistenceSphereChart q s 0) hx
    (mfderiv (𝓡 3) Ic (capPersistenceSphereChart q s) 0 v)).1
  rw [capPersistenceSphereChart_model] at hc
  have hmodel : ‖v‖ ^ 2 ≤ stereographicCylinderCoefficients 2 0 v v := by
    rw [stereographicCylinderCoefficients_apply, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_three]
    norm_num only [stereographicCylinderDensity, stereographicCylinderDenominator,
      PiLp.zero_apply, zero_pow (by decide : 2 ≠ 0), zero_add, add_zero,
      OfNat.ofNat_ne_zero, div_self]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  apply (mul_le_mul_of_nonneg_left hmodel (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
  change (1 / 2 : ℝ) * stereographicCylinderCoefficients 2 0 v v ≤
    N.scale⁻¹ ^ 2 * g.inner _
      (mfderiv (𝓡 3) (𝓡 3) (N.capPersistenceEuclideanMap q s) 0 v)
      (mfderiv (𝓡 3) (𝓡 3) (N.capPersistenceEuclideanMap q s) 0 v)
  rw [N.capPersistenceEuclideanMap_mfderiv q s hx]
  exact hc

end PoincareConjecture.EpsilonNeck
