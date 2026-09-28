import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Realization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.EpsilonNeck

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

def centeredEuclideanParametrization (N : EpsilonNeck g) (q : UnitTwoSphere)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : M :=
  N.centeredParametrization q ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x)

@[simp] theorem centeredEuclideanParametrization_zero (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) :
    N.centeredEuclideanParametrization q s 0 = N.coordinate_map (q, s) := by
  simp only [centeredEuclideanParametrization, map_zero, add_zero,
    centeredParametrization, sphere_chart_symm_zero]

theorem centeredEuclideanParametrization_contMDiffAt (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (N.centeredEuclideanParametrization q s) x := by
  have hcoord : ContDiff ℝ ∞
      (fun y => (0, s) + (RiemannianMetric.lineModelEquiv 2).symm y) :=
    contDiff_const.add (RiemannianMetric.lineModelEquiv 2).symm.contDiff
  exact (N.centeredParametrization_contMDiffAt q hx).comp x hcoord.contMDiff.contMDiffAt

theorem centeredEuclideanParametrization_mfderiv (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) x v =
      mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (N.centeredParametrization q)
        ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x)
          ((RiemannianMetric.lineModelEquiv 2).symm v) := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap
  have h : HasFDerivAt (fun y => (0, s) + T y) T x := by
    simpa only [Pi.add_def, zero_add] using (hasFDerivAt_const (0, s) x).add T.hasFDerivAt
  have hm : mfderiv (𝓡 3) 𝓘(ℝ, RoundCylinderCoordinates)
      (fun y => (0, s) + T y) x = T := by
    rw [mfderiv_eq_fderiv]
    exact h.fderiv
  change mfderiv (𝓡 3) (𝓡 3)
    (N.centeredParametrization q ∘ (fun y => (0, s) + T y)) x v = _
  rw [mfderiv_comp x ((N.centeredParametrization_contMDiffAt q hx).mdifferentiableAt
    (by simp)) h.differentiableAt.mdifferentiableAt, hm]
  rfl

theorem normalizedEuclideanCoefficients_eq_pullback (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v w : EuclideanSpace ℝ (Fin 3)) :
    N.normalizedEuclideanCoefficients q s x v w =
      N.scale⁻¹ ^ 2 * g.inner (N.centeredEuclideanParametrization q s x)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) x v)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) x w) := by
  rw [N.centeredEuclideanParametrization_mfderiv q s hx,
    N.centeredEuclideanParametrization_mfderiv q s hx]
  rfl

theorem normalized_realization_curvature
    (N : EpsilonNeck g) (D' : LeviCivitaData g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) :
    D.scalarCurvature 0 = N.scale ^ 2 * D'.scalarCurvature (N.coordinate_map (q, s)) ∧
      ∀ v w : EuclideanSpace ℝ (Fin 3),
        D.ricci 0 v w = D'.ricci (N.centeredEuclideanParametrization q s 0)
          (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 v)
          (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 w) := by
  let F := N.centeredEuclideanParametrization q s
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add (RiemannianMetric.lineModelEquiv 2).symm.continuous))
  have h0U : 0 ∈ U := by simpa only [U, mem_ofPred_eq, map_zero, add_zero] using hs
  obtain ⟨V, hV, hVo, h0V⟩ := mem_nhds_iff.mp (heq.and (hU.mem_nhds h0U))
  have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F V := fun x hx =>
    (N.centeredEuclideanParametrization_contMDiffAt q s (hV hx).2).contMDiffWithinAt
  have hc : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let DN := rescaledMetric_connection g D' (N.scale⁻¹ ^ 2) hc
  have hmetric : ∀ x ∈ V, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner x v w = (rescaledMetric g (N.scale⁻¹ ^ 2) hc).inner (F x)
        (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x w) := by
    intro x hx v w
    change h.euclideanCoefficients x v w = _
    rw [(hV hx).1, N.normalizedEuclideanCoefficients_eq_pullback q s (hV hx).2,
      rescaledMetric_inner]
  constructor
  · have hscalar := D.scalarCurvature_eq_of_local_isometry DN hVo hF hmetric h0V
    simpa only [DN, rescaledMetric_scalarCurvature, inv_pow, inv_inv, F,
      centeredEuclideanParametrization_zero] using hscalar
  · intro v w
    have hricci := D.ricci_eq_of_local_isometry DN hVo hF hmetric h0V v w
    simpa only [DN, rescaledMetric_ricci, F] using hricci

end PoincareConjecture.EpsilonNeck
