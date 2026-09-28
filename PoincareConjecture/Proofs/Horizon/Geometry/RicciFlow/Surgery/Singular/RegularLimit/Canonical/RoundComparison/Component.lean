import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.SphereModel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

def roundComparisonThreshold : ℝ := min roundScalarTolerance (1 / 200)

theorem roundComparisonThreshold_pos : 0 < roundComparisonThreshold :=
  lt_min roundScalarTolerance_pos (by norm_num)

theorem roundComparisonThreshold_le : roundComparisonThreshold ≤ 1 / 200 := min_le_right _ _

end PoincareConjecture.SingularRegularLimit.RoundComparison

namespace PoincareConjecture.SingularRoundComponent

open SingularRegularLimit.RoundComparison

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ}

theorem forward_mfderiv_injective (N : SingularRoundComponent g epsilon)
    (x : N.model.carrier) : Function.Injective (mfderiv (𝓡 3) (𝓡 3) N.forward x) := by
  have hopen : IsOpen N.carrier := N.forward_image ▸ N.forward_openEmbedding.isOpen_range
  have hx : N.forward x ∈ N.carrier := N.forward_image ▸ mem_range_self x
  have hi := N.inverse_smooth.contMDiffAt (hopen.mem_nhds hx)
  have hchain := mfderiv_comp x (hi.mdifferentiableAt (by simp))
    ((N.forward_smooth x).mdifferentiableAt (by simp))
  have heq : N.inverse ∘ N.forward = id := funext N.left_inverse
  rw [heq, mfderiv_id] at hchain
  intro v w hvw
  have h := congrArg (fun z => mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x) z) hvw
  change ((mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x)).comp
    (mfderiv (𝓡 3) (𝓡 3) N.forward x)) v =
    ((mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x)).comp
      (mfderiv (𝓡 3) (𝓡 3) N.forward x)) w at h
  rw [← hchain] at h
  exact h

def normalizedMetric (N : SingularRoundComponent g epsilon) :
    RiemannianMetric 3 N.model.carrier :=
  RiemannianMetric.Induced.pullbackMetric (rescaledMetric g N.scale N.scale_pos)
    N.forward N.forward_smooth N.forward_mfderiv_injective

theorem normalizedMetric_inner (N : SingularRoundComponent g epsilon)
    (x : N.model.carrier) (v w : TangentSpace (𝓡 3) x) :
    N.normalizedMetric.inner x v w = N.scale * g.inner (N.forward x)
      (mfderiv (𝓡 3) (𝓡 3) N.forward x v)
      (mfderiv (𝓡 3) (𝓡 3) N.forward x w) := rfl

theorem normalizedMetric_scalar (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g) (x : N.model.carrier) :
    N.normalizedMetric.leviCivitaData.scalarCurvature x =
      N.scale⁻¹ * D.scalarCurvature (N.forward x) := by
  have h := N.normalizedMetric.leviCivitaData.scalarCurvature_eq_of_local_isometry
    (rescaledMetric_connection g D N.scale N.scale_pos) isOpen_univ
    N.forward_smooth.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)
  simpa only [rescaledMetric_scalarCurvature] using h

theorem normalizedMetric_error_norm_lt (N : SingularRoundComponent g epsilon)
    {r : ℕ} (hr : r ≤ ⌊epsilon⁻¹⌋₊) (x : N.model.carrier) :
    N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          N.normalizedMetric.inner y (v 0) (v 1) -
            N.model_metric.inner y (v 0) (v 1)) r) x < epsilon := by
  obtain ⟨b, hb, hbound⟩ := N.metric_comparison
  have hterm := Finset.single_le_sum
    (s := Finset.range (⌊epsilon⁻¹⌋₊ + 1)) (a := r)
    (f := fun j => (N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative
        (fun y v => N.scale * singularMetricPullback g N.forward y v -
          N.model_metric.inner y (v 0) (v 1)) j) x) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  have hs := hterm.trans_lt ((hbound x).trans_lt hb)
  change (N.model_metric.tensorNorm
    (N.model_connection.iteratedCovariantTensorDerivative
      (fun y v => N.normalizedMetric.inner y (v 0) (v 1) -
        N.model_metric.inner y (v 0) (v 1)) r) x) ^ 2 < epsilon ^ 2 at hs
  nlinarith [N.epsilon_pos]

theorem normalized_scalar_close (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g) (hepsilon : epsilon ≤ roundComparisonThreshold)
    (x : N.model.carrier) :
    |N.scale⁻¹ * D.scalarCurvature (N.forward x) - 6| < 1 := by
  let : CompactSpace N.model.carrier := isCompact_univ_iff.mp N.model_compact
  have htwo : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply (Nat.le_floor_iff (inv_nonneg.mpr N.epsilon_pos.le)).mpr
    rw [inv_eq_one_div, le_div_iff₀ N.epsilon_pos]
    have he := hepsilon.trans roundComparisonThreshold_le
    norm_num
    linarith
  have h := scalar_close_of_unit_curvature N.model_connection
    N.normalizedMetric.leviCivitaData N.model_curvature_one x (fun r hr =>
      (N.normalizedMetric_error_norm_lt (hr.trans htwo) x).trans_le
        (hepsilon.trans (min_le_left _ _)))
  rwa [N.normalizedMetric_scalar D x] at h

theorem scalar_le_two_mul (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g) (hepsilon : epsilon ≤ roundComparisonThreshold)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    D.scalarCurvature y ≤ 2 * D.scalarCurvature x := by
  have hx' := N.normalized_scalar_close D hepsilon (N.inverse x)
  have hy' := N.normalized_scalar_close D hepsilon (N.inverse y)
  rw [N.right_inverse hx] at hx'
  rw [N.right_inverse hy] at hy'
  have hlx := (abs_lt.mp hx').1
  have huy := (abs_lt.mp hy').2
  have hh : N.scale⁻¹ * D.scalarCurvature y ≤
      N.scale⁻¹ * (2 * D.scalarCurvature x) := by linarith
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr N.scale_pos)).mp hh

end PoincareConjecture.SingularRoundComponent
