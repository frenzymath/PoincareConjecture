import PoincareConjecture.Proofs.M47.CanonicalNeckScalarComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open M36 M44 M45 Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem cap_neck_normalized_metric_realization (N : EpsilonNeck g)
    (q : UnitTwoSphere) {c : ℝ}
    (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1) (U : Set E),
      IsOpen U ∧ M35.cylinderCoordinateEquiv.symm (0, c) ∈ U ∧
      (∀ y ∈ U, ∀ i j : Fin 3,
        g1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
          roundCylinderPullback g N.coordinate_map z v w) (chartAt E2 q)
          (M35.cylinderCoordinateEquiv y) i j) ∧
      D1.scalarCurvature (M35.cylinderCoordinateEquiv.symm (0, c)) =
        N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c)) := by
  let p := M35.cylinderCoordinateEquiv.symm ((0, c) : RoundCylinderCoordinates)
  let f := centeredNeckLift N q 0
  let V := centeredNeckDomain N 0
  have hV : IsOpen V := centeredNeckDomain_isOpen N 0
  have hp : p ∈ V := by
    change (M35.cylinderCoordinateEquiv p).2 + 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply, add_zero] using hc
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V := fun y hy =>
    (centeredNeckLift_contMDiffAt N q 0 hy).contMDiffWithinAt
  have hinv : ∀ y ∈ V, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    fun y hy => centeredNeckLift_mfderiv_isInvertible N q 0 hy
  obtain ⟨gE, DE, U, hU, hpU, hUV, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hV hp (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (centeredNeckLift_contMDiffAt N q 0 hy)).contDiffWithinAt)
      (fun y _ v w => g.symm (f y) _ _)
      (fun y hy v hv => by
        apply g.pos (f y)
        intro h
        apply hv
        exact (hinv y hy).injective (h.trans (map_zero _).symm))
  have hQ : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let gQ := m01RescaledMetric gE (N.scale⁻¹ ^ 2) hQ
  let DQ := m01RescaledMetric_connection gE DE (N.scale⁻¹ ^ 2) hQ
  refine ⟨gQ, DQ, U, hU, hpU, ?_, ?_⟩
  · intro y hy i j
    have hnative : gQ.euclideanCoefficients y = centeredCylinderMetric
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
          q 0 y := by
      calc
        gQ.euclideanCoefficients y = N.scale⁻¹ ^ 2 • gE.euclideanCoefficients y := rfl
        _ = N.scale⁻¹ ^ 2 • g.pullbackCoefficients f y :=
          congrArg (fun B => N.scale⁻¹ ^ 2 • B) (hmetric y hy)
        _ = (m01RescaledMetric g (N.scale⁻¹ ^ 2) hQ).pullbackCoefficients f y := rfl
        _ = _ := scaled_neck_pullback_coefficients N g hQ q 0 (hUV hy)
    have h := congrArg (fun B => B (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)) hnative
    rw [centeredCylinderMetric, centeredCylinderBilinear_basis] at h
    simp only [RiemannianMetric.euclideanCoefficients, cylinderEuclideanEquiv,
      show ((0 : E2), (0 : ℝ)) = 0 from rfl, add_zero] at h
    convert! h using 1
  · have hscalar : DE.scalarCurvature p = N.connection.scalarCurvature (f p) :=
      DE.scalarCurvature_eq_of_local_isometry N.connection hU (hf.mono hUV)
        (fun y hy v w => congrArg (fun B => B v w) (hmetric y hy)) hpU
    have hscale : DQ.scalarCurvature p = DE.scalarCurvature p / (N.scale⁻¹ ^ 2) := by
      have h := M13.homothety_scalarCurvature_eq gE gQ
        (Diffeomorph.refl (𝓡 3) E ∞) (N.scale⁻¹ ^ 2) hQ
        (rescaledMetric_identity_homothety hQ) DE DQ p
      simpa only [Diffeomorph.coe_refl, id_eq] using h
    have hfp : f p = N.coordinate_map (q, c) := by
      have hchart : centeredCylinderLift q 0 p = (q, c) := by
        change ((chartAt E2 q).symm (M35.cylinderCoordinateEquiv p).1,
          (M35.cylinderCoordinateEquiv p).2 + 0) = (q, c)
        dsimp only [p]
        rw [ContinuousLinearEquiv.apply_symm_apply, add_zero]
        apply Prod.ext
        · rw [← sphere_chart_center_zero q]
          exact (chartAt E2 q).left_inv (mem_chart_source E2 q)
        · rfl
      exact congrArg N.coordinate_map hchart
    change DQ.scalarCurvature p = _
    rw [hscale, hscalar, hfp, inv_pow, div_inv_eq_mul, mul_comm]

end PoincareConjecture.M47
