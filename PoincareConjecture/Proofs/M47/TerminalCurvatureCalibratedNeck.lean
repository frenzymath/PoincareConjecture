import PoincareConjecture.Proofs.M47.TerminalCurvatureNeckNative
import PoincareConjecture.Proofs.M47.TerminalCurvatureNumericalPlane
import PoincareConjecture.Proofs.M47.TerminalCurvatureModelAngular
import PoincareConjecture.Proofs.M47.CanonicalNeckModelFrame
import PoincareConjecture.Proofs.M47.TerminalCurvatureNeckSphere
import PoincareConjecture.Proofs.M01.NormalizationCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M36 PoincareConjecture.Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_calibrated_neck_positive_plane
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 200) (theta : UnitTwoSphere) :
    ∃ a b : TangentSpace (𝓡 2) theta,
      0 < D.curvatureTensor (N.coordinate_map (theta, 0))
        (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta a)
        (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta b)
        (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta a)
        (mfderiv (𝓡 2) (𝓡 3) (fun theta => N.coordinate_map (theta, 0)) theta b) := by
  let D0 := M35.cylinderEuclideanConnection 0 (by norm_num)
  obtain ⟨g1, D1, U, hU, h0, hdomain, hcoeff, hb0, hb1, hb2⟩ :=
    terminalCurvature_exists_neck_native_realization N theta D0
  have hz : M35.cylinderCoordinateEquiv.symm ((0, 0) : RoundCylinderCoordinates) = 0 := by
    exact M35.cylinderCoordinateEquiv.symm.map_zero
  have he (v w : E) :
      (M35.cylinderEuclideanMetric 0 (by norm_num)).inner 0
        (neckModelFrame v) (neckModelFrame w) = inner ℝ v w := by
    convert! neckModelFrame_isometry 0 v w using 1
    exact congrArg (fun y : E =>
      (M35.cylinderEuclideanMetric 0 (by norm_num)).euclideanCoefficients y
        (neckModelFrame v) (neckModelFrame w)) hz.symm
  have hnormal (v w : E) : D0.euclideanConnection v w 0 = 0 := by
    simpa only [hz] using cap_model_connection_normal 0 (by norm_num) D0 theta 0 v w
  have hsquare : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have he0 : neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 0) =
      (Real.sqrt 2)⁻¹ • EuclideanSpace.basisFun (Fin 3) ℝ 0 := by
    simpa only [Fin.reduceEq, if_false] using neckModelFrame_basis 0
  have he1 : neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 1) =
      (Real.sqrt 2)⁻¹ • EuclideanSpace.basisFun (Fin 3) ℝ 1 := by
    simpa only [Fin.reduceEq, if_false] using neckModelFrame_basis 1
  have hmodel := terminalCurvature_model_angular_vector D0 theta 0
    (Real.sqrt 2)⁻¹ hsquare neckModelFrame he0 he1
  rw [hz] at hmodel
  let e0 := neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 0)
  let e1 := neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 1)
  have hpositive : 0 < D1.curvatureTensor 0 e0 e1 e0 e1 := by
    exact lt_trans (by norm_num : (0 : ℝ) < 1 / 4)
      (terminalCurvature_calibrated_angular_plane D0 D1 0 neckModelFrame he hnormal
        hmodel N.epsilon_pos.le hsmall hb0 hb1 hb2)
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have h0domain := zero_mem_centeredNeckDomain N hzero
  have hpull := D1.curvatureTensor_eq_pullback_euclidean (normalizedNeckConnection N)
    (centeredNeckLift_contMDiffAt N theta 0 h0domain)
    (by
      filter_upwards [(centeredNeckDomain_isOpen N 0).mem_nhds h0domain] with x hx
      exact centeredNeckLift_mfderiv_isInvertible N theta 0 hx)
    (by
      filter_upwards [hU.mem_nhds h0] with x hx
      intro v w
      exact congrArg (fun B => B v w) (hcoeff x hx)) e0 e1 e0 e1
  rw [hpull, normalizedNeckConnection, m01RescaledMetric_curvatureTensor] at hpositive
  have hneck := (mul_pos_iff_of_pos_left N.scalar_center_pos).mp hpositive
  have heq := D.curvatureTensor_eq_of_local_isometry N.connection (f := id)
    isOpen_univ contMDiff_id.contMDiffOn
    (fun x _ v w => by simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply])
    (mem_univ (centeredNeckLift N theta 0 0))
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1)
  simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] at heq
  have hactual := heq.symm ▸ hneck
  have hheight0 : cylinderHeightCovector e0 = 0 := by
    dsimp only [e0]
    rw [he0, map_smul, cylinderHeightCovector_basis]
    norm_num [roundCylinderCoordinateBasis]
  have hheight1 : cylinderHeightCovector e1 = 0 := by
    dsimp only [e1]
    rw [he1, map_smul, cylinderHeightCovector_basis]
    norm_num [roundCylinderCoordinateBasis]
  refine ⟨mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) theta).symm 0
      (cylinderHorizontalProjection e0),
    mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) theta).symm 0
      (cylinderHorizontalProjection e1), ?_⟩
  rw [terminalCurvature_neck_sphere_horizontal N theta e0 hheight0,
    terminalCurvature_neck_sphere_horizontal N theta e1 hheight1]
  let v0 : E := mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e0
  let v1 : E := mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta 0) 0 e1
  have hpoint := congrArg (fun x : M => D.curvatureTensor x v0 v1 v0 v1)
    (centeredNeckLift_zero N theta 0)
  exact hpoint ▸ hactual

end PoincareConjecture.M47
