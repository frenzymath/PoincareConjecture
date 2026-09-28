import PoincareConjecture.Proofs.M36.SurgeryTransitionChart
import PoincareConjecture.Proofs.M36.CenteredNeckMetric
import PoincareConjecture.Proofs.M36.PolarContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem adaptedPolarPoint_bilinear_end (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : g₀.cylindrical_end.radius < z.2)
    (v w : StandardCylinderCoordinates) :
    g₀.metric.inner (adaptedPolarPoint g₀ z)
      (mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z v)
      (mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z w) =
        RoundCylinderMetric z v w := by
  let T : StandardCylinderSpace → StandardCylinderSpace :=
    fun q => (q.1, q.2 - g₀.cylindrical_end.radius)
  have hT : ContMDiff IC IC ∞ T :=
    contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
  have hE := (cylindrical_coordinate_contMDiffAt g₀ (T z)
    (by dsimp [T]; linarith [g₀.cylindrical_end.collar_pos])).mdifferentiableAt (by simp)
  have heq : adaptedPolarPoint g₀ =ᶠ[𝓝 z] g₀.cylindrical_end.coordinate ∘ T := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with q hq
    exact adaptedPolarPoint_eq_end g₀ q hq.le
  have hd := heq.mfderiv_eq (I := IC) (I' := 𝓡 3)
  rw [mfderiv_comp z hE ((hT z).mdifferentiableAt (by simp))] at hd
  have hdv (a : StandardCylinderCoordinates) :
      mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z a =
        mfderiv IC (𝓡 3) g₀.cylindrical_end.coordinate (T z) a := by
    have ha := congrArg (fun D => D a) hd
    change mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z a =
      mfderiv IC (𝓡 3) g₀.cylindrical_end.coordinate (T z)
        (mfderiv IC IC T z a) at ha
    rwa [show mfderiv IC IC T z a = a from cylinder_height_translation_mfderiv _ z a] at ha
  rw [hdv v, hdv w, adaptedPolarPoint_eq_end g₀ z hz.le]
  exact g₀.cylindrical_end.metric_pullback (T z) (sub_nonneg.mpr hz.le) v w

theorem adaptedClippedCollapse_bilinear_transition (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : z.2 < 2) (v w : StandardCylinderCoordinates) :
    g₀.metric.inner (adaptedClippedCollapse g₀ (surgeryCapRadius g₀) z)
      (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) z v)
      (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) z w) =
        RoundCylinderMetric z v w := by
  let T : StandardCylinderSpace → StandardCylinderSpace :=
    fun q => (q.1, surgeryCapRadius g₀ - q.2)
  have hT : ContMDiff IC IC ∞ T :=
    contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  have htip : z.2 < surgeryCapRadius g₀ := by
    dsimp [surgeryCapRadius]
    linarith [g₀.cylindrical_end.radius_pos]
  have hend : g₀.cylindrical_end.radius < (T z).2 := by
    dsimp [T, surgeryCapRadius]
    linarith
  have heq : adaptedClippedCollapse g₀ (surgeryCapRadius g₀) =ᶠ[𝓝 z]
      adaptedPolarPoint g₀ ∘ T := by
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds htip] with q hq
    exact adaptedClippedCollapse_of_lt g₀ _ q hq
  have hd := heq.mfderiv_eq (I := IC) (I' := 𝓡 3)
  rw [mfderiv_comp z ((adaptedPolarPoint_contMDiff g₀ (T z)).mdifferentiableAt (by simp))
    ((hT z).mdifferentiableAt (by simp))] at hd
  have hdv (a : StandardCylinderCoordinates) :
      mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) z a =
        mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) (T z) (a.1, -a.2) := by
    have ha := congrArg (fun D => D a) hd
    change mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) z a =
      mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) (T z) (mfderiv IC IC T z a) at ha
    rwa [show mfderiv IC IC T z a = (a.1, -a.2) from
      cylinder_height_reversal_mfderiv _ z a] at ha
  rw [hdv v, hdv w, adaptedClippedCollapse_of_lt g₀ _ z htip]
  rw [adaptedPolarPoint_bilinear_end g₀ (T z) hend]
  change 2 * (1 - (0 : ℝ)) * _ + (-v.2) * (-w.2) =
    2 * (1 - (0 : ℝ)) * _ + v.2 * w.2
  ring

theorem centeredCylinderLift_basis_gram (theta : UnitTwoSphere) (s : ℝ)
    (p : E₃) (i j : Fin 3) :
    RoundCylinderMetric (centeredCylinderLift theta s p)
      (mfderiv (𝓡 3) IC (centeredCylinderLift theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (mfderiv (𝓡 3) IC (centeredCylinderLift theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      cylinderModelField p (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  rw [← centeredCylinderBilinear_gram theta s, centeredCylinderBilinear_basis,
    centeredCylinderLift_mfderiv, centeredCylinderLift_mfderiv]
  have hcoord : cylinderEuclideanEquiv p + (0, s) =
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
    apply Prod.ext
    · exact add_zero _
    · rfl
  have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).1 :=
    congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
  rw [hcoord]
  simp only [roundCylinderGram, roundCylinderTensorCoefficient, cylinderHeightCovector_basis, hP]
  rfl

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem surgeryTransitionBackground_pullbackCoefficients (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ) {p : E₃}
    (hp : p ∈ centeredSurgeryDomain N s) :
    g₀.metric.pullbackCoefficients
      (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) ∘
        centeredSurgeryLift g₀ N theta s) p = cylinderModelField p := by
  let A := centeredCylinderLift theta s
  let F := surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) ∘
    centeredSurgeryLift g₀ N theta s
  have htip : (A p).2 < surgeryCapRadius g₀ := by
    change cylinderHeightCovector p + s < g₀.cylindrical_end.radius + 4
    exact hp.2.trans (by linarith [g₀.cylindrical_end.radius_pos])
  have hclip := ((adaptedClippedCollapse_contMDiffOn g₀ _ (A p) htip).contMDiffAt
    ((isOpen_lt continuous_snd continuous_const).mem_nhds htip)).mdifferentiableAt (by simp)
  have hA := ((centeredCylinderLift_contMDiff theta s) p).mdifferentiableAt (by simp)
  have heq : F =ᶠ[𝓝 p] adaptedClippedCollapse g₀ (surgeryCapRadius g₀) ∘ A := by
    filter_upwards [(centeredSurgeryDomain_isOpen N s).mem_nhds hp] with q hq
    exact centeredSurgeryLift_inclusion g₀ N theta s hq
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp p hclip hA] at hd
  apply euclideanThree_bilinear_ext
  intro i j
  change g₀.metric.inner (F p)
    (mfderiv (𝓡 3) (𝓡 3) F p (EuclideanSpace.basisFun (Fin 3) ℝ i))
    (mfderiv (𝓡 3) (𝓡 3) F p (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [show F p = adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (A p) from
    centeredSurgeryLift_inclusion g₀ N theta s hp, hd]
  simp only [ContinuousLinearMap.comp_apply]
  rw [adaptedClippedCollapse_bilinear_transition g₀ (A p) hp.2]
  exact centeredCylinderLift_basis_gram theta s p i j

theorem surgeryNeckWeight_centeredSurgeryLift (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ) {p : E₃}
    (hp : p ∈ centeredSurgeryDomain N s) :
    surgeryNeckWeight g₀ N (centeredSurgeryLift g₀ N theta s p) =
      neckCutoff (cylinderHeightCovector p + s) := by
  change neckCutoff (standardSurgeryHeight g₀
    (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
      (centeredSurgeryLift g₀ N theta s p))) = _
  rw [centeredSurgeryLift_height g₀ N theta s hp]

theorem surgeryConformalMultiplier_centeredSurgeryLift (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (C q : ℝ) {r : ℝ} (hr : 0 < r)
    (hrA : r ≤ g₀.cylindrical_end.radius)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s) :
    surgeryConformalMultiplier g₀ N C q r (centeredSurgeryLift g₀ N theta s p) =
      Real.exp (-2 * smoothProfile C q N.epsilon (cylinderHeightCovector p + s)) := by
  have hheight := centeredSurgeryLift_height g₀ N theta s hp
  have htwo : standardSurgeryHeight g₀
      (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
        (centeredSurgeryLift g₀ N theta s p)) ≤ 2 := by
    rw [hheight]
    exact hp.2.le
  change radialConformalMultiplier g₀ C q N.epsilon r
    (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
      (centeredSurgeryLift g₀ N theta s p)) = _
  rw [radialConformalMultiplier_eq_on_transition g₀ C q N.epsilon hr hrA htwo,
    hheight]
  rfl

theorem surgeryMetric_pullbackCoefficients_transition (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (C q eta r : ℝ) (hlambda : 0 < N.connection.scalarCurvature N.center)
    (heta : 0 < eta) (hr : 0 < r) (hrA : r ≤ g₀.cylindrical_end.radius)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredSurgeryDomain N s) :
    (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).pullbackCoefficients
      (centeredSurgeryLift g₀ N theta s) p =
      (N.connection.scalarCurvature N.center)⁻¹ •
        (Real.exp (-2 * smoothProfile C q N.epsilon (cylinderHeightCovector p + s)) •
          (neckCutoff (cylinderHeightCovector p + s) •
              centeredCylinderMetric (fun z v w => normalizedNeckForm N z v w) theta s p +
            (1 - neckCutoff (cylinderHeightCovector p + s)) • (eta • cylinderModelField p))) := by
  have hL := (centeredSurgeryLift_contMDiffAt g₀ N theta s hp).mdifferentiableAt (by simp)
  have hI := ((surgeryBallInclusion_contMDiff g₀ (surgeryOuterRadius g₀ N.epsilon))
    (centeredSurgeryLift g₀ N theta s p)).mdifferentiableAt (by simp)
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hbg := congrArg (fun A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => A v w)
    (surgeryTransitionBackground_pullbackCoefficients g₀ N theta s hp)
  change g₀.metric.inner
    (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
      (centeredSurgeryLift g₀ N theta s p))
    (mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) ∘
      centeredSurgeryLift g₀ N theta s) p v)
    (mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) ∘
      centeredSurgeryLift g₀ N theta s) p w) = cylinderModelField p v w at hbg
  rw [mfderiv_comp p hI hL] at hbg
  change g₀.metric.inner
    (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)
      (centeredSurgeryLift g₀ N theta s p))
    (mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon))
      (centeredSurgeryLift g₀ N theta s p)
      (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p v))
    (mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon))
      (centeredSurgeryLift g₀ N theta s p)
      (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p w)) =
        cylinderModelField p v w at hbg
  have hneck := congrArg (fun A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => A v w)
    (normalizedNeckMetric_pullbackCoefficients N theta s hp.1)
  change N.connection.scalarCurvature N.center * g.inner (centeredNeckLift N theta s p)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p v)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p w) =
      centeredCylinderMetric (fun z a b => normalizedNeckForm N z a b) theta s p v w at hneck
  change (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner
    (centeredSurgeryLift g₀ N theta s p)
    (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p v)
    (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p w) = _
  rw [surgeryMetric_inner, surgeryNeckWeight_centeredSurgeryLift g₀ N theta s hp,
    surgeryConformalMultiplier_centeredSurgeryLift g₀ N C q hr hrA theta s hp]
  simp only [metricPullbackForm_apply,
    surgeryRetainedInverse_centeredSurgeryLift_mfderiv g₀ N hcut theta s hp]
  erw [surgeryRetainedInverse_centeredSurgeryLift g₀ N theta s hp, hbg]
  simp only [smul_apply, add_apply, smul_eq_mul]
  erw [← hneck]
  field_simp [hlambda.ne']

end PoincareConjecture.M36
