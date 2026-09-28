import PoincareConjecture.Proofs.M47.CanonicalNeckCoarseReadout
import PoincareConjecture.Proofs.M47.BlowupControlsCapModelScalar
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.ChangeMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

open M36 M44 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem neck_pullback_scalar_difference_le {g0 : RiemannianMetric 3 M}
    (N : EpsilonNeck g0) (hsmall : N.epsilon ≤ 1 / 200)
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {Q u : ℝ} (hQ : 0 < Q) (hu : u ≤ 0)
    (hclose : RoundCylinderClose N.epsilon u
      (fun z v w => Q * roundCylinderPullback g N.coordinate_map z v w))
    (x : M) (hx : x ∈ N.carrier) :
    |D.scalarCurvature x / Q - 1 / (1 - u)| ≤ (16 / 5 : ℝ) * N.epsilon := by
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  let p := M35.cylinderCoordinateEquiv.symm ((0, z.2) : RoundCylinderCoordinates)
  let f := centeredNeckLift N z.1 0
  let U := centeredNeckDomain N 0
  have hU : IsOpen U := centeredNeckDomain_isOpen N 0
  have hp : p ∈ U := by
    change (M35.cylinderCoordinateEquiv p).2 + 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply, add_zero] using hz
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U := fun y hy =>
    (centeredNeckLift_contMDiffAt N z.1 0 hy).contMDiffWithinAt
  have hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    fun y hy => centeredNeckLift_mfderiv_isInvertible N z.1 0 hy
  obtain ⟨gE, DE, W, hW, hpW, hWU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hU hp (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (centeredNeckLift_contMDiffAt N z.1 0 hy)).contDiffWithinAt)
      (fun y _ v w => g.symm (f y) _ _)
      (fun y hy v hv => by
        apply g.pos (f y)
        intro h
        apply hv
        exact (hinv y hy).injective (h.trans (map_zero _).symm))
  let gQ := m01RescaledMetric gE Q hQ
  let DQ := m01RescaledMetric_connection gE DE Q hQ
  let D0 := DQ.withMetric (M35.cylinderEuclideanMetric u (by linarith))
  have hcoeff (y : E) (hy : y ∈ W) (i j : Fin 3) :
      gQ.inner y (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient
        (fun z v w => Q * roundCylinderPullback g N.coordinate_map z v w)
        (chartAt E2 z.1) (M35.cylinderCoordinateEquiv y) i j := by
    have hnative : gQ.euclideanCoefficients y = centeredCylinderMetric
        (fun z v w => Q * roundCylinderPullback g N.coordinate_map z v w) z.1 0 y := by
      calc
        gQ.euclideanCoefficients y = Q • gE.euclideanCoefficients y := rfl
        _ = Q • g.pullbackCoefficients f y := congrArg (fun B => Q • B) (hmetric y hy)
        _ = (m01RescaledMetric g Q hQ).pullbackCoefficients f y := rfl
        _ = _ := scaled_neck_pullback_coefficients N g hQ z.1 0 (hWU hy)
    have h := congrArg (fun B => B (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)) hnative
    rw [centeredCylinderMetric, centeredCylinderBilinear_basis] at h
    simp only [RiemannianMetric.euclideanCoefficients, cylinderEuclideanEquiv,
      show ((0 : E2), (0 : ℝ)) = 0 from rfl, add_zero] at h
    convert! h using 1
  have hscalar : DE.scalarCurvature p = D.scalarCurvature (f p) :=
    DE.scalarCurvature_eq_of_local_isometry D hW (hf.mono hWU)
      (fun y hy v w => congrArg (fun B => B v w) (hmetric y hy)) hpW
  have hscale : DQ.scalarCurvature p = DE.scalarCurvature p / Q := by
    have h := M13.homothety_scalarCurvature_eq gE gQ (Diffeomorph.refl (𝓡 3) E ∞)
      Q hQ (rescaledMetric_identity_homothety hQ) DE DQ p
    simpa only [Diffeomorph.coe_refl, id_eq] using h
  have hfp : f p = x := by
    have hc : centeredCylinderLift z.1 0 p = z := by
      change ((chartAt E2 z.1).symm (M35.cylinderCoordinateEquiv p).1,
        (M35.cylinderCoordinateEquiv p).2 + 0) = z
      dsimp only [p]
      rw [ContinuousLinearEquiv.apply_symm_apply, add_zero]
      apply Prod.ext
      · rw [← sphere_chart_center_zero z.1]
        exact (chartAt E2 z.1).left_inv (mem_chart_source E2 z.1)
      · rfl
    change N.coordinate_map (centeredCylinderLift z.1 0 p) = x
    rw [hc]
    exact neck_coordinate_inverse N hx
  have h := PoincareConjecture.M47.cap_model_scalar_difference_le N.epsilon_pos hsmall hu
    _ hclose gQ DQ D0 z.1 hW hcoeff z.2 hz hpW
  change |DQ.scalarCurvature p - 1 / (1 - u)| ≤ _ at h
  rwa [hscale, hscalar, hfp] at h

end PoincareConjecture.Proofs.M47
