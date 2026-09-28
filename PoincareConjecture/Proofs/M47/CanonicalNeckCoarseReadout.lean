import PoincareConjecture.Proofs.M47.CanonicalNeckCoarseScalar
import PoincareConjecture.Proofs.M45.Ch9_Models.NeckBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M36 M44 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]


theorem scaled_neck_pullback_coefficients {g0 : RiemannianMetric 3 M}
    (N : EpsilonNeck g0) (g : RiemannianMetric 3 M) {Q : ℝ} (hQ : 0 < Q)
    (theta : UnitTwoSphere) (s : ℝ) {p : E} (hp : p ∈ centeredNeckDomain N s) :
    (m01RescaledMetric g Q hQ).pullbackCoefficients (centeredNeckLift N theta s) p =
      centeredCylinderMetric
        (fun z v w => Q * roundCylinderPullback g N.coordinate_map z v w) theta s p := by
  apply euclideanThree_bilinear_ext
  intro i j
  rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
  have hcoord : cylinderEuclideanEquiv p + (0, s) =
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
    apply Prod.ext
    · exact add_zero _
    · rfl
  rw [hcoord]
  change Q * g.inner (centeredNeckLift N theta s p)
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [centeredNeckLift_mfderiv N theta s hp, centeredNeckLift_mfderiv N theta s hp]
  have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).1 :=
    congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
  simp only [roundCylinderTensorCoefficient, cylinderHeightCovector_basis, hP]
  rfl


theorem exists_neck_pullback_scalar_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M],
      ∀ {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0), N.epsilon ≤ 1 / 200 →
      ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g) {Q t : ℝ}, 0 < Q →
        t ∈ Icc (-1 : ℝ) 0 →
        RoundCylinderClose N.epsilon t
          (fun z v w => Q * roundCylinderPullback g N.coordinate_map z v w) →
        ∀ x ∈ N.carrier, |D.scalarCurvature x| ≤ C * Q := by
  obtain ⟨C, hC, hbound⟩ := exists_negativeCylinder_realized_scalar_bound
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g0 N hsmall g D Q t hQ ht hclose x hx
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  let f := centeredNeckLift N z.1 z.2
  let U := centeredNeckDomain N z.2
  have hU : IsOpen U := centeredNeckDomain_isOpen N z.2
  have hzero : (0 : E) ∈ U := zero_mem_centeredNeckDomain N hz
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U := fun y hy =>
    (centeredNeckLift_contMDiffAt N z.1 z.2 hy).contMDiffWithinAt
  have hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    fun y hy => centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hy
  obtain ⟨gE, DE, W, hW, hzeroW, hWU, hmetric⟩ :=
    model_metric_realization g hU hzero hf hinv
  let gQ := m01RescaledMetric gE Q hQ
  let DQ := m01RescaledMetric_connection gE DE Q hQ
  have hcoeff : gQ.euclideanCoefficients =ᶠ[𝓝 0]
      centeredCylinderMetric
        (fun z v w => Q * roundCylinderPullback g N.coordinate_map z v w) z.1 z.2 := by
    filter_upwards [hW.mem_nhds hzeroW] with y hy
    calc
      gQ.euclideanCoefficients y = Q • gE.euclideanCoefficients y := rfl
      _ = Q • g.pullbackCoefficients f y := congrArg (fun A => Q • A) (hmetric y hy)
      _ = (m01RescaledMetric g Q hQ).pullbackCoefficients f y := rfl
      _ = _ := scaled_neck_pullback_coefficients N g hQ z.1 z.2 (hWU hy)
  have hscalar : DE.scalarCurvature 0 = D.scalarCurvature (f 0) :=
    DE.scalarCurvature_eq_of_local_isometry D hW (hf.mono hWU)
      (fun y hy v w => congrArg (fun B => B v w) (hmetric y hy)) hzeroW
  have hscale : DQ.scalarCurvature 0 = DE.scalarCurvature 0 / Q := by
    have h := M13.homothety_scalarCurvature_eq gE gQ (Diffeomorph.refl (𝓡 3) E ∞)
      Q hQ (rescaledMetric_identity_homothety hQ) DE DQ 0
    simpa only [Diffeomorph.coe_refl, id_eq] using h
  have hfzero : f 0 = x := by
    rw [show f 0 = N.coordinate_map (z.1, z.2) from centeredNeckLift_zero N z.1 z.2]
    exact neck_coordinate_inverse N hx
  have h := hbound N.epsilon_pos hsmall ht hclose z hz gQ DQ hcoeff
  rw [hscale, hscalar, hfzero, abs_div, abs_of_pos hQ] at h
  exact (div_le_iff₀ hQ).mp h

end PoincareConjecture.Proofs.M47
