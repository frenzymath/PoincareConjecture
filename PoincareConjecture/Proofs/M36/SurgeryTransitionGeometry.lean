import PoincareConjecture.Proofs.M36.SurgeryTransitionMetric
import PoincareConjecture.Proofs.M36.CylinderBlend
import PoincareConjecture.Proofs.M36.CylinderJetEstimates
import PoincareConjecture.Proofs.M36.StandardCapTransfer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u v

namespace PoincareConjecture.M36

open PoincareConjecture.SpacetimeBounds

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

section LocalGeometry

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace E₃ X] [ChartedSpace E₃ Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]
  {g : RiemannianMetric 3 X} {h : RiemannianMetric 3 Y}

theorem scalarCurvature_eq_of_local_isometry (D : LeviCivitaData g)
    (D' : LeviCivitaData h) {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ x ∈ U, ∀ a b : TangentSpace (𝓡 3) x,
      g.inner x a b = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x a)
        (mfderiv (𝓡 3) (𝓡 3) f x b)) {x : X} (hx : x ∈ U) :
    D.scalarCurvature x = D'.scalarCurvature (f x) := by
  let e : TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 3) (𝓡 3) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : Y → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  rw [scalarCurvature_eq_sum_orthonormal D x (g.orthonormalBasis x),
    scalarCurvature_eq_sum_orthonormal D' (f x) ((g.orthonormalBasis x).map e')]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx
    (g.orthonormalBasis x i) (g.orthonormalBasis x j)
    (g.orthonormalBasis x i) (g.orthonormalBasis x j)

structure CylinderPointBounds (D : LeviCivitaData g) (s : X → ℝ) (x : X)
    (B : ℝ) : Prop where
  gradient : 1 / 2 ≤ g.inner x (D.gradient s x) (D.gradient s x) ∧
    g.inner x (D.gradient s x) (D.gradient s x) ≤ 2
  hessian : ∀ a b : TangentSpace (𝓡 3) x,
    |D.hessian s x a b| ≤ B * g.tangentNorm x a * g.tangentNorm x b
  laplacian : |D.laplacian s x| ≤ B
  scalar : 1 / 2 ≤ D.scalarCurvature x
  sectional : ∀ a b : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x a b → -B ≤ D.sectionalCurvature x a b
  axial : ∀ a b : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x a b →
    (mvfderiv (𝓡 3) s x a) ^ 2 + (mvfderiv (𝓡 3) s x b) ^ 2 ≤ 1 / 2 →
    1 / 8 ≤ D.sectionalCurvature x a b

end LocalGeometry

theorem cylinderPointBounds_transport
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace E₃ Y] [IsManifold (𝓡 3) ∞ Y]
    {gE : RiemannianMetric 3 E₃} {gY : RiemannianMetric 3 Y}
    (DE : LeviCivitaData gE) (DY : LeviCivitaData gY)
    {f : E₃ → Y} {V : Set E₃} (hV : IsOpen V) (hzero : (0 : E₃) ∈ V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V)
    (hinv : ∀ p ∈ V, (mfderiv (𝓡 3) (𝓡 3) f p).IsInvertible)
    (hmetric : ∀ p ∈ V, ∀ a b : E₃, gE.inner p a b =
      gY.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p a) (mfderiv (𝓡 3) (𝓡 3) f p b))
    {height : Y → ℝ} (hheight : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ height (f 0))
    (s : ℝ) (heq : height ∘ f =ᶠ[𝓝 (0 : E₃)] fun p => cylinderHeightCovector p + s)
    {B : ℝ} (hb : CylinderPointBounds DE cylinderHeightCovector 0 B) :
    CylinderPointBounds DY height (f 0) B := by
  have hf0 := (hf 0 hzero).contMDiffAt (hV.mem_nhds hzero)
  have hi : ∀ᶠ p in 𝓝 (0 : E₃), (mfderiv (𝓡 3) (𝓡 3) f p).IsInvertible := by
    filter_upwards [hV.mem_nhds hzero] with p hp using hinv p hp
  have hm : ∀ᶠ p in 𝓝 (0 : E₃), ∀ a b : TangentSpace (𝓡 3) p,
      gE.inner p a b = gY.inner (f p)
        (mfderiv (𝓡 3) (𝓡 3) f p a) (mfderiv (𝓡 3) (𝓡 3) f p b) := by
    filter_upwards [hV.mem_nhds hzero] with p hp using hmetric p hp
  have hd : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ cylinderHeightCovector (0 : E₃) :=
    cylinderHeightCovector.contDiff.contMDiff.contMDiffAt
  have hgrad : DE.gradient (height ∘ f) 0 = DE.gradient cylinderHeightCovector 0 := by
    have h := gradient_scalar_profile_germ DE
      (phi := fun t : ℝ => t + s) (differentiableAt_id.add_const s)
      (hd.mdifferentiableAt (by simp)) heq
    simpa only [deriv_add_const, deriv_id'', one_smul] using h
  have hhess (a b : E₃) : DE.hessian (height ∘ f) 0 a b =
      DE.hessian cylinderHeightCovector 0 a b := by
    have h := hessian_scalar_profile_germ DE (phi := fun t : ℝ => t + s)
      (contDiff_id.add contDiff_const) hd heq a b
    simpa only [deriv_add_const', deriv_id'', deriv_const', one_mul, zero_mul, add_zero] using h
  have hlap : DE.laplacian (height ∘ f) 0 = DE.laplacian cylinderHeightCovector 0 := by
    unfold LeviCivitaData.laplacian
    simp only [hhess]
  have hgradNorm : gE.inner 0 (DE.gradient cylinderHeightCovector 0)
      (DE.gradient cylinderHeightCovector 0) =
      gY.inner (f 0) (DY.gradient height (f 0)) (DY.gradient height (f 0)) := by
    rw [← hgrad, DE.gradient_comp_eq_mpullback DY
      (hf0.mdifferentiableAt (by simp)) (hheight.mdifferentiableAt (by simp))
      hi.self_of_nhds (hmetric 0 hzero), hmetric 0 hzero]
    simp only [VectorField.mpullback, hi.self_of_nhds.self_apply_inverse]
  have hdheight (a : E₃) : mvfderiv (𝓡 3) height (f 0)
      (mfderiv (𝓡 3) (𝓡 3) f 0 a) = cylinderHeightCovector a := by
    have he := congrArg (fun D => D a)
      (heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓘(ℝ, ℝ)))
    rw [mfderiv_comp 0 (hheight.mdifferentiableAt (by simp))
      (hf0.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
      (cylinderHeightCovector.hasFDerivAt.add_const s).fderiv] at he
    exact he
  have hpair (a b : TangentSpace (𝓡 3) (f 0))
      (hab : LeviCivitaData.IsOrthonormalPair gY (f 0) a b) :
      LeviCivitaData.IsOrthonormalPair gE 0
        ((mfderiv (𝓡 3) (𝓡 3) f 0).inverse a)
        ((mfderiv (𝓡 3) (𝓡 3) f 0).inverse b) := by
    unfold LeviCivitaData.IsOrthonormalPair
    rw [hmetric 0 hzero, hmetric 0 hzero, hmetric 0 hzero]
    simpa only [LeviCivitaData.IsOrthonormalPair,
      hi.self_of_nhds.self_apply_inverse] using hab
  have hsec (a b : TangentSpace (𝓡 3) (f 0)) :
      DE.sectionalCurvature 0 ((mfderiv (𝓡 3) (𝓡 3) f 0).inverse a)
        ((mfderiv (𝓡 3) (𝓡 3) f 0).inverse b) = DY.sectionalCurvature (f 0) a b := by
    rw [sectionalCurvature_eq_of_local_isometry DE DY hV hf hmetric hzero]
    simp only [hi.self_of_nhds.self_apply_inverse]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hgradNorm] using hb.gradient
  · apply DE.abs_hessian_le_of_metric_pullback DY hf0 hi hm hheight
    intro a b
    rw [hhess]
    exact hb.hessian a b
  · rw [← DE.laplacian_comp_of_metric_pullback DY hf0 hi hm hheight, hlap]
    exact hb.laplacian
  · rw [← scalarCurvature_eq_of_local_isometry DE DY hV hf hmetric hzero]
    exact hb.scalar
  · intro a b hab
    rw [← hsec]
    exact hb.sectional _ _ (hpair a b hab)
  · intro a b hab haxial
    rw [← hsec]
    apply hb.axial _ _ (hpair a b hab)
    have ha := hdheight ((mfderiv (𝓡 3) (𝓡 3) f 0).inverse a)
    have hb' := hdheight ((mfderiv (𝓡 3) (𝓡 3) f 0).inverse b)
    simp only [hi.self_of_nhds.self_apply_inverse] at ha hb'
    rw [cylinderHeightCovector_mvfderiv, cylinderHeightCovector_mvfderiv, ← ha, ← hb']
    exact haxial

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

noncomputable def surgeryOutputHeight (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) → ℝ :=
  standardSurgeryHeight g₀ ∘ surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)

theorem surgeryOutputHeight_continuous (g₀ : StandardInitialMetric) (N : EpsilonNeck g) :
    Continuous (surgeryOutputHeight g₀ N) :=
  (standardSurgeryHeight_continuous g₀).comp (surgeryBallInclusion_contMDiff g₀ _).continuous

theorem surgeryOutputHeight_contMDiffAt (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : surgeryOutputHeight g₀ N y < 2) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (surgeryOutputHeight g₀ N) y := by
  have hne : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y ≠ 0 := by
    intro hz
    change standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) < 2 at hy
    rw [hz, standardSurgeryHeight_zero] at hy
    linarith [g₀.cylindrical_end.radius_pos]
  exact (standardSurgeryHeight_contDiffAt g₀ hne).contMDiffAt.comp y
    (surgeryBallInclusion_contMDiff g₀ _ y)

noncomputable def surgeryPreconformalMetric (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (eta : ℝ) (heta : 0 < eta) :
    RiemannianMetric 3 (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :=
  weightedPullbackMetric (normalizedNeckMetric N)
    (positiveScaling (surgeryBackgroundMetric g₀ N) (fun _ => eta)
      contMDiff_const (fun _ => heta))
    (surgeryRetainedInverse g₀ N) (surgeryNeckWeight g₀ N) (surgeryTransitionDomain g₀ N)
    (surgeryTransitionDomain_isOpen g₀ N) (surgeryNeckWeight_contMDiff g₀ N)
    (fun y => radialNeckWeight_bounds g₀ (surgeryBallInclusion g₀ _ y))
    (surgeryNeckWeight_tsupport g₀ N)
    (fun _ hy => surgeryRetainedInverse_contMDiffAt g₀ N hcut
      (surgeryTransitionDomain_ne_zero g₀ N hy))
    (fun _ hy => surgeryRetainedInverse_mfderiv_bijective g₀ N hcut
      (surgeryTransitionDomain_ne_zero g₀ N hy))

theorem surgeryPreconformalMetric_inner (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (eta : ℝ) (heta : 0 < eta)
    (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
    (v w : TangentSpace (𝓡 3) y) :
    (surgeryPreconformalMetric g₀ N hcut eta heta).inner y v w =
      surgeryNeckWeight g₀ N y *
        (N.connection.scalarCurvature N.center *
          metricPullbackForm g (surgeryRetainedInverse g₀ N) y v w) +
        (1 - surgeryNeckWeight g₀ N y) *
          (eta * metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y v w) := rfl

theorem surgeryMetric_preconformal_inner (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (C q eta r : ℝ) (hlambda : 0 < N.connection.scalarCurvature N.center)
    (heta : 0 < eta) (hr : 0 < r)
    (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
    (v w : TangentSpace (𝓡 3) y) :
    N.connection.scalarCurvature N.center *
      (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner y v w =
        surgeryConformalMultiplier g₀ N C q r y *
          (surgeryPreconformalMetric g₀ N hcut eta heta).inner y v w := by
  rw [surgeryMetric_inner, surgeryPreconformalMetric_inner]
  field_simp [hlambda.ne']

theorem surgeryPreconformalMetric_pullbackCoefficients (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (heta : 0 < 1 - 6 * N.epsilon) (theta : UnitTwoSphere) (s : ℝ) {p : E₃}
    (hp : p ∈ centeredSurgeryDomain N s) :
    (surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta).pullbackCoefficients
      (centeredSurgeryLift g₀ N theta s) p =
      cylinderBlend N.epsilon
        (centeredCylinderMetric (fun z a b => normalizedNeckForm N z a b) theta s) s p := by
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
  change (surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta).inner
    (centeredSurgeryLift g₀ N theta s p)
    (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p v)
    (mfderiv (𝓡 3) (𝓡 3) (centeredSurgeryLift g₀ N theta s) p w) = _
  rw [surgeryPreconformalMetric_inner, surgeryNeckWeight_centeredSurgeryLift g₀ N theta s hp]
  simp only [metricPullbackForm_apply,
    surgeryRetainedInverse_centeredSurgeryLift_mfderiv g₀ N hcut theta s hp]
  erw [surgeryRetainedInverse_centeredSurgeryLift g₀ N theta s hp, hbg, hneck]
  rfl

theorem exists_surgeryPreconformalGeometry :
    ∃ delta : ℝ, 0 < delta ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ (g₀ : StandardInitialMetric)
        {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g),
        ∀ (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹), N.epsilon ≤ delta →
        ∀ (heta : 0 < 1 - 6 * N.epsilon)
          (D : LeviCivitaData (surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta))
          (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)),
          0 ≤ surgeryOutputHeight g₀ N y → surgeryOutputHeight g₀ N y < 2 →
          CylinderPointBounds D (surgeryOutputHeight g₀ N) y (K * N.epsilon) := by
  obtain ⟨delta, hd, K, hK, hgeometry⟩ := exists_cylinderMetric_uniform_estimates
  obtain ⟨L, hL, hblend⟩ := exists_cylinderBlend_twoJet_bound
  have hLp : 0 < L := by linarith only [hL]
  refine ⟨min (delta / L) (1 / 4), by positivity, K * L,
    one_le_mul_of_one_le_of_one_le hK hL, ?_⟩
  intro g₀ M _ _ _ g N hcut hsmall heta D y hy0 hy2
  obtain ⟨theta, s, hzero, hezero, hs⟩ := exists_centeredSurgeryLift_zero g₀ N hcut hy2
  let e := centeredSurgeryLift g₀ N theta s
  let J := surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta
  obtain ⟨gE, DE, V, hV, h0V, hVU, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization (centeredSurgeryDomain_isOpen N s) hzero
      (J.pullbackCoefficients e)
      (fun p hp => (J.contDiffAt_pullbackCoefficients
        (centeredSurgeryLift_contMDiffAt g₀ N theta s hp)).contDiffWithinAt)
      (fun p _ a b => J.symm (e p) _ _)
      (fun p hp a ha => by
        apply J.pos (e p)
        intro heq
        apply ha
        apply (centeredSurgeryLift_mfderiv_isInvertible g₀ N hcut theta s hp).injective
        rw [map_zero]
        exact heq)
  have hfield : gE.euclideanCoefficients =ᶠ[𝓝 (0 : E₃)]
      cylinderBlend N.epsilon
        (centeredCylinderMetric (fun z a b => normalizedNeckForm N z a b) theta s) s := by
    filter_upwards [hV.mem_nhds h0V] with p hp
    exact (hcoeff p hp).trans
      (surgeryPreconformalMetric_pullbackCoefficients g₀ N hcut heta theta s (hVU hp))
  have hjet := show metricTwoJet gE.euclideanCoefficients 0 = metricTwoJet
      (cylinderBlend N.epsilon
        (centeredCylinderMetric (fun z a b => normalizedNeckForm N z a b) theta s) s) 0 by
    simp only [metricTwoJet, hfield.self_of_nhds, hfield.fderiv_eq,
      (hfield.fderiv (𝕜 := ℝ)).fderiv_eq]
  have horder : 2 ≤ ⌊N.epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    have hi := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 4) N.epsilon_pos).mpr
      (hsmall.trans (min_le_right _ _))
    norm_num at hi ⊢
    linarith
  have hs0 : 0 ≤ s := by rw [hs]; exact hy0
  have hs2 : s < 2 := by rw [hs]; exact hy2
  have hsneck : s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [centeredNeckDomain, Set.mem_ofPred_eq, map_zero, zero_add] using hzero.1
  have herr : ‖metricTwoJet gE.euclideanCoefficients 0 - cylinderModelJet‖ ≤ L * N.epsilon := by
    rw [hjet]
    exact hblend N.epsilon N.epsilon_pos _ N.metric_comparison.close horder
      (theta, s) ⟨hs0, hs2.le⟩ hsneck
  have hesmall : L * N.epsilon ≤ delta := by
    have h := (le_div_iff₀ hLp).mp (hsmall.trans (min_le_left _ _))
    nlinarith only [h]
  obtain ⟨hG, hH, hLap, hR, hSec, hGap⟩ := hgeometry gE DE (L * N.epsilon)
    (mul_nonneg hLp.le N.epsilon_pos.le) hesmall herr
  have hbounds : CylinderPointBounds DE cylinderHeightCovector 0 (K * (L * N.epsilon)) := by
    refine ⟨hG, hH, hLap, hR, ?_, ?_⟩
    · intro a b hab
      simpa only [neg_mul] using hSec a b hab
    · intro a b hab haxial
      apply hGap a b hab
      simpa only [cylinderHeightCovector_mvfderiv] using haxial
  have heq : surgeryOutputHeight g₀ N ∘ e =ᶠ[𝓝 (0 : E₃)]
      fun p => cylinderHeightCovector p + s := by
    filter_upwards [(centeredSurgeryDomain_isOpen N s).mem_nhds hzero] with p hp
    exact centeredSurgeryLift_height g₀ N theta s hp
  have hyLift : surgeryOutputHeight g₀ N (e 0) < 2 := by
    change surgeryOutputHeight g₀ N (centeredSurgeryLift g₀ N theta s 0) < 2
    rw [hezero]
    exact hy2
  have hresult := cylinderPointBounds_transport DE D hV h0V
    (fun p hp => (centeredSurgeryLift_contMDiffAt g₀ N theta s (hVU hp)).contMDiffWithinAt)
    (fun p hp => centeredSurgeryLift_mfderiv_isInvertible g₀ N hcut theta s (hVU hp))
    (fun p hp a b => congrArg (fun A => A a b) (hcoeff p hp))
    (surgeryOutputHeight_contMDiffAt g₀ N hyLift)
    s heq hbounds
  simpa only [hezero, mul_assoc] using hresult

end PoincareConjecture.M36
