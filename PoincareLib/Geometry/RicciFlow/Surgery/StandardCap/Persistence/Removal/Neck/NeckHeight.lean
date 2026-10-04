import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Neck.NeckBufferTopology
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.NeckMetricBound
import PoincareLib.Geometry.Riemannian.ScalarOperators.Euclidean

/-!
# The inverse height differential of the later neck

The actual M36 metric comparison bounds the inverse height
differential in physical units. Embedding height in a Euclidean
axis gives the map used by the ambient length barrier.
Morgan--Tian, Claim 16.10, pp. 374-375; M44 derivation 71.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "axis" => EuclideanSpace.basisFun (Fin 3) ℝ 2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The inverse height differential obeys the physical quadratic
bound from the neck comparison. Source: Claim 16.10;
M44 derivation 71. -/
theorem neck_inverse_height_quadratic (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 12) {x : M} (hx : x ∈ N.carrier)
    (w : TangentSpace (𝓡 3) x) :
    ((1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center) *
      ((mfderiv (𝓡 3) IC N.coordinate_inverse x w).2) ^ 2 ≤ g.inner x w w := by
  let e := neckPartialDiffeomorph N
  have hD : e.toOpenPartialHomeomorph.MDifferentiable IC (𝓡 3) :=
    ⟨e.mdifferentiableOn (by simp), e.symm.mdifferentiableOn (by simp)⟩
  have hcancel : mfderiv IC (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
      (mfderiv (𝓡 3) IC N.coordinate_inverse x w) = w :=
    congrArg (fun L => L w) (hD.comp_symm_deriv hx)
  let v := mfderiv (𝓡 3) IC N.coordinate_inverse x w
  have hbound := normalizedNeckForm_lower N (N.coordinate_inverse x)
    (N.coordinate_inverse_mem x hx).2 v
  rw [normalizedNeckForm_apply] at hbound
  change (1 - 6 * N.epsilon) * (2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2) ≤
    N.connection.scalarCurvature N.center *
      g.inner (N.coordinate_map (N.coordinate_inverse x))
        (mfderiv IC (𝓡 3) N.coordinate_map (N.coordinate_inverse x) v)
        (mfderiv IC (𝓡 3) N.coordinate_map (N.coordinate_inverse x) v) at hbound
  rw [hcancel, neck_coordinate_inverse N hx] at hbound
  change ((1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center) * v.2 ^ 2 ≤ _
  rw [div_mul_eq_mul_div, div_le_iff₀ N.scalar_center_pos]
  have hnonneg : 0 ≤ 1 - 6 * N.epsilon := by linarith
  nlinarith [mul_nonneg hnonneg (add_nonneg (sq_nonneg (v.1 0)) (sq_nonneg (v.1 1)))]

/-- The neck's actual inverse height as a Euclidean axis map.
Source: the length buffer in Claim 16.10; M44 derivation 71. -/
noncomputable def neckHeightVector (N : EpsilonNeck g) (x : M) : E :=
  (N.coordinate_inverse x).2 • axis

/-- The height axis map is smooth at every actual neck point.
Source: Claim 16.10; M44 derivation 71. -/
theorem neckHeightVector_contMDiffAt (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (neckHeightVector N) x := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight axis
  exact L.contMDiff.contMDiffAt.comp x (neck_inverse_contMDiffAt N hx).snd

/-- The derivative of the height axis map is exactly the axial
part of the primitive inverse differential. Source: Claim 16.10;
M44 derivation 71. -/
theorem neckHeightVector_mfderiv (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (w : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (neckHeightVector N) x w =
      (mfderiv (𝓡 3) IC N.coordinate_inverse x w).2 • axis := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight axis
  have hi := ((neck_inverse_contMDiffAt N hx).mdifferentiableAt (by simp)).hasMFDerivAt
  have hp := (hasMFDerivAt_snd (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))
    (N.coordinate_inverse x)).comp x hi
  have h := L.hasMFDerivAt.comp x hp
  exact congrArg (fun D => D w) h.mfderiv

/-- The Euclidean axis metric, weighted by the neck's physical
factor, is dominated by the actual metric on its full carrier.
Source: Claim 16.10, pp. 374-375; M44 derivation 71. -/
theorem neckHeightVector_quadratic (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 12) {x : M} (hx : x ∈ N.carrier)
    (w : TangentSpace (𝓡 3) x) :
    ((1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center) *
      (RiemannianMetric.euclideanMetric 3).inner (neckHeightVector N x)
        (mfderiv (𝓡 3) (𝓡 3) (neckHeightVector N) x w)
        (mfderiv (𝓡 3) (𝓡 3) (neckHeightVector N) x w) ≤ g.inner x w w := by
  rw [RiemannianMetric.euclideanMetric_inner, neckHeightVector_mfderiv N hx,
    real_inner_self_eq_norm_sq]
  simpa only [norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one,
    mul_one, sq_abs] using neck_inverse_height_quadratic N hsmall hx w

end PoincareMT.M44
