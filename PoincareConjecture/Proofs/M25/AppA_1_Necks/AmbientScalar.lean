import PoincareConjecture.Proofs.M25.AppA_1_Necks.GermRealization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



noncomputable def euclideanParametrization (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : M :=
  N.centeredParametrization q ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x)



theorem euclideanParametrization_contMDiffAt (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (N.euclideanParametrization q s) x := by
  exact (N.centeredParametrization_contMDiffAt q hx).comp x
    ((contDiff_const.add (RiemannianMetric.lineModelEquiv 2).symm.contDiff).contMDiff x)



theorem euclideanParametrization_zero (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) :
    N.euclideanParametrization q s 0 = N.coordinate_map (q, s) := by
  simp only [euclideanParametrization, map_zero, add_zero, centeredParametrization,
    Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero]



theorem normalizedEuclideanCoefficients_pullback (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v w : EuclideanSpace ℝ (Fin 3)) :
    N.m25_normalizedEuclideanCoefficients q s x v w =
      N.scale⁻¹ ^ 2 * g.inner (N.euclideanParametrization q s x)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x v)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x w) := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let phi := fun y : EuclideanSpace ℝ (Fin 3) => (0, s) + T y
  have hphi : HasFDerivAt phi T.toContinuousLinearMap x := T.hasFDerivAt.const_add (0, s)
  have hN := (N.centeredParametrization_contMDiffAt q hx).mdifferentiableAt (by simp)
  have hder : mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x =
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (N.centeredParametrization q) (phi x)).comp T.toContinuousLinearMap := by
    change mfderiv (𝓡 3) (𝓡 3) (N.centeredParametrization q ∘ phi) x = _
    rw [mfderiv_comp x hN hphi.differentiableAt.mdifferentiableAt,
      mfderiv_eq_fderiv, hphi.fderiv]
  simp only [m25_normalizedEuclideanCoefficients, RiemannianMetric.parameterBilinearEquiv_apply,
    normalizedCenteredCoefficients, smul_apply, smul_eq_mul,
    RiemannianMetric.parametrizedCoefficients_apply, hder]
  rfl



theorem realization_scalar_eq (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ)
    (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData h)
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V) (h0 : 0 ∈ V)
    (hstrip : ∀ x ∈ V, ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (heq : ∀ x ∈ V, h.euclideanCoefficients x = N.m25_normalizedEuclideanCoefficients q s x) :
    D.scalarCurvature 0 =
      N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, s)) := by
  have hc : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let Dc := rescaledMetric_connection g N.connection (N.scale⁻¹ ^ 2) hc
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (N.euclideanParametrization q s) V :=
    fun x hx => (N.euclideanParametrization_contMDiffAt q s (hstrip x hx)).contMDiffWithinAt
  have hm (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ V)
      (v w : TangentSpace (𝓡 3) x) :
      h.inner x v w = (rescaledMetric g (N.scale⁻¹ ^ 2) hc).inner
        (N.euclideanParametrization q s x)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x v)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x w) := by
    change h.euclideanCoefficients x v w = _
    rw [heq x hx, rescaledMetric_inner]
    exact N.normalizedEuclideanCoefficients_pullback q s (hstrip x hx) v w
  have hscalar := D.scalarCurvature_eq_of_local_isometry Dc hV hf hm h0
  rw [rescaledMetric_scalarCurvature, N.euclideanParametrization_zero] at hscalar
  simpa only [inv_pow, inv_inv] using hscalar

end PoincareConjecture.EpsilonNeck
