import PoincareConjecture.Proofs.M47.CanonicalNeckScalarComparison
import PoincareConjecture.Proofs.M34.Standard.LocalPullbackRealization
import PoincareConjecture.Proofs.M34.Standard.LocalHomothetyCurvature
import PoincareConjecture.Proofs.M34.Standard.NeckRestriction
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M36 M44 M45 Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
  {origin scale : ℝ} {I : Set ℝ}
  (e : SurgeryFlowCylinder F C origin scale I N.carrier)

theorem source_neck_slice_metric_realization (s : ℝ) (hs : s ∈ I)
    (q : UnitTwoSphere) {c : ℝ} (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1) (W : Set E),
      IsOpen W ∧ M35.cylinderCoordinateEquiv.symm (0, c) ∈ W ∧
      (∀ y ∈ W, ∀ i j : Fin 3,
        g1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        roundCylinderTensorCoefficient (surgeryCylinderPullback e N.coordinate_map s)
          (chartAt E2 q) (M35.cylinderCoordinateEquiv y) i j) ∧
      D1.scalarCurvature (M35.cylinderCoordinateEquiv.symm (0, c)) =
        (F.connection (origin + s / scale)).scalarCurvature
          (e.forward s hs (N.coordinate_map (q, c))) / scale := by
  let p := M35.cylinderCoordinateEquiv.symm ((0, c) : RoundCylinderCoordinates)
  let V := centeredNeckDomain N 0
  let f := e.forward s hs ∘ centeredNeckLift N q 0
  let chart := cylinderSliceChart e N.carrier_open s hs
  have hV : IsOpen V := centeredNeckDomain_isOpen N 0
  have hp : p ∈ V := by
    change (M35.cylinderCoordinateEquiv p).2 + 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply, add_zero] using hc
  have hmem (y : E) (hy : y ∈ V) : centeredNeckLift N q 0 y ∈ N.carrier :=
    centeredNeckLift_mem N q 0 hy
  have hnative (y : E) (hy : y ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (centeredNeckLift N q 0) y :=
    centeredNeckLift_contMDiffAt N q 0 hy
  have hforward (y : E) (hy : y ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (e.forward s hs) (centeredNeckLift N q 0 y) :=
    (e.forward_smooth s hs).contMDiffAt (N.carrier_open.mem_nhds (hmem y hy))
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V := fun y hy =>
    ((hforward y hy).comp y (hnative y hy)).contMDiffWithinAt
  have hchain (y : E) (hy : y ∈ V) :
      mfderiv (𝓡 3) (𝓡 3) f y =
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (centeredNeckLift N q 0 y)).comp
          (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q 0) y) :=
    mfderiv_comp y ((hforward y hy).mdifferentiableAt (by simp))
      ((hnative y hy).mdifferentiableAt (by simp))
  have hinj (y : E) (hy : y ∈ V) :
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) := by
    have hi : (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs)
        (centeredNeckLift N q 0 y)).IsInvertible :=
      ⟨(chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hmem y hy)).mfderivToContinuousLinearEquiv
        (by simp), rfl⟩
    rw [hchain y hy]
    exact hi.injective.comp (centeredNeckLift_mfderiv_isInvertible N q 0 hy).injective
  let gQ := m01RescaledMetric (F.metric (origin + s / scale)) scale e.scale_pos
  obtain ⟨g1, D1, W, hW, hpW, hWV, hmetric⟩ :=
    gQ.exists_local_immersive_pullback_realization f hV hp hf hinj
  have hmetricQ (y : E) (hy : y ∈ W) (v w : TangentSpace (𝓡 3) y) :
      g1.inner y v w = scale * (F.metric (origin + s / scale)).inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) :=
    congrArg (fun B => B v w) (hmetric y hy)
  refine ⟨g1, D1, W, hW, hpW, ?_, ?_⟩
  · intro y hy i j
    have hcoeff : g1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        roundCylinderTensorCoefficient (surgeryCylinderPullback e N.coordinate_map s)
          (chartAt E2 q) (cylinderEuclideanEquiv y + (0, 0)) i j := by
      have hcoord : cylinderEuclideanEquiv y + (0, 0) =
          (cylinderHorizontalProjection y, cylinderHeightCovector y + 0) := by
        apply Prod.ext
        · exact add_zero _
        · rfl
      rw [hcoord, hmetricQ y hy]
      have hd (k : Fin 3) : mfderiv (𝓡 3) (𝓡 3) f y
          (EuclideanSpace.basisFun (Fin 3) ℝ k) =
          mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (centeredNeckLift N q 0 y)
            (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q 0) y
              (EuclideanSpace.basisFun (Fin 3) ℝ k)) :=
        congrArg (fun A => A (EuclideanSpace.basisFun (Fin 3) ℝ k)) (hchain y (hWV hy))
      rw [hd i, hd j]
      simp only [centeredNeckLift_mfderiv N q 0 (hWV hy)]
      have hP (k : Fin 3) :
          cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
            (roundCylinderCoordinateBasis k).1 :=
        congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
      simp only [roundCylinderTensorCoefficient, surgeryCylinderPullback, dif_pos hs,
        SurgeryFlowCylinder.pullbackInner, cylinderHeightCovector_basis, hP]
      rfl
    simp only [cylinderEuclideanEquiv, show ((0 : E2), (0 : ℝ)) = 0 from rfl,
      add_zero] at hcoeff
    convert! hcoeff using 1
  · have hscalar := D1.scalarCurvature_eq_of_local_homothety
      (F.connection (origin + s / scale)) e.scale_pos hW (hf.mono hWV) hmetricQ hpW
    have hpoint : centeredNeckLift N q 0 p = N.coordinate_map (q, c) := by
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
    change D1.scalarCurvature p = _
    simpa only [f, Function.comp_apply, hpoint] using hscalar

theorem source_neck_slice_scalar_difference_le (hsmall : N.epsilon ≤ 1 / 200)
    (s : ℝ) (hs : s ∈ I) (hs0 : s ≤ 0)
    (hclose : RoundCylinderClose N.epsilon s (surgeryCylinderPullback e N.coordinate_map s))
    {x : C.carrier} (hx : x ∈ N.carrier) :
    |(F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) / scale -
        1 / (1 - s)| ≤ (16 / 5 : ℝ) * N.epsilon := by
  let z := N.coordinate_inverse x
  have hz := (N.coordinate_inverse_mem x hx).2
  obtain ⟨g1, D1, W, hW, hpW, hcoeff, hscalar⟩ :=
    source_neck_slice_metric_realization N e s hs z.1 hz
  let D0 := D1.withMetric (M35.cylinderEuclideanMetric s (by linarith))
  have h := cap_model_scalar_difference_le N.epsilon_pos hsmall hs0 _ hclose
    g1 D1 D0 z.1 hW hcoeff z.2 hz hpW
  rw [hscalar] at h
  have hpoint : N.coordinate_map (z.1, z.2) = x := neck_coordinate_inverse N hx
  rwa [hpoint] at h

theorem source_initial_old_scalar_difference_le
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (i : Fin (F.event T hT).cap_count) (old : SurgeryTerminalStrongNeck F T hT i)
    (hsmall : F.parameters.delta T ≤ 1 / 200) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    {x : (F.event T hT).terminal.carrier} (hx : x ∈ ((F.event T hT).necks i).neck.carrier) :
    |(F.connection (T + s / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2))).scalarCurvature
        (old.cylinder.forward s hs x) / (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) -
      1 / (1 - s)| ≤ (16 / 5 : ℝ) * F.parameters.delta T := by
  have hclose := old.comparison.at_time (show s ∈ Ioc (-1 : ℝ) 0 from ⟨hs.1, hs.2.le⟩)
  rw [if_neg hs.2.ne] at hclose
  have hdelta := (F.event T hT).neck_delta i
  have h := source_neck_slice_scalar_difference_le ((F.event T hT).necks i).neck
    old.cylinder (hdelta.trans_le hsmall) s hs hs.2.le (hdelta.symm ▸ hclose) hx
  simpa only [hdelta] using h

end PoincareConjecture.M47
