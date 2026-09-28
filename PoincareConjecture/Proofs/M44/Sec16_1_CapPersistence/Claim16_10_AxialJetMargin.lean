import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance axialCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance axialCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance axialTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance axialTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem continuousAt_jetChristoffel_family {X : Type*} [TopologicalSpace X]
    {J : X → MetricTwoJet 3} {u v : X → E} {p : X}
    (hJ : ContinuousAt J p) (hinv : (J p).1.IsInvertible)
    (hu : ContinuousAt u p) (hv : ContinuousAt v p) :
    ContinuousAt (fun z => jetChristoffel (J z) (u z) (v z)) p := by
  have hI0 : ContinuousAt (fun A : MetricCoefficient 3 => A.inverse) (J p).1 :=
    (hinv.contDiffAt_map_inverse (n := ∞)).continuousAt
  have hI : ContinuousAt (fun z => (J z).1.inverse) p :=
    hI0.comp (f := fun z : X => (J z).1) hJ.fst
  have hf : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
  have hf' : Continuous (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous
  unfold jetChristoffel metricKoszulCovector
  fun_prop

theorem continuousAt_jetCurvature_family {X : Type*} [TopologicalSpace X]
    {J : X → MetricTwoJet 3} {u w v z : X → E} {p : X}
    (hJ : ContinuousAt J p) (hinv : (J p).1.IsInvertible)
    (hu : ContinuousAt u p) (hw : ContinuousAt w p)
    (hv : ContinuousAt v p) (hz : ContinuousAt z p) :
    ContinuousAt (fun a => jetCurvature (J a) (u a) (w a) (v a) (z a)) p := by
  have hΓ1 := continuousAt_jetChristoffel_family hJ hinv hw hz
  have hΓ2 := continuousAt_jetChristoffel_family hJ hinv hu hz
  have hΓ3 := continuousAt_jetChristoffel_family hJ hinv hu hΓ1
  have hΓ4 := continuousAt_jetChristoffel_family hJ hinv hw hΓ2
  unfold jetCurvature
  fun_prop

theorem cylinderModelJet_axialGram {u : E} (hu : ‖u‖ = 1)
    (hh : cylinderHeightCovector u = 0) :
    collarJetGram (e 2) u (evolvingCylinderModelJet 0) = 2 := by
  have hP : cylinderHorizontalProjection (e 2) = 0 := by
    change (cylinderEuclideanEquiv (e 2)).1 = 0
    rw [cylinderEuclideanEquiv_basis]
    rfl
  have hH0 : cylinderHorizontalForm (e 2) (e 2) = 0 := by
    change inner ℝ (cylinderHorizontalProjection (e 2))
      (cylinderHorizontalProjection (e 2)) = 0
    rw [hP, inner_zero_left]
  have hH1 : cylinderHorizontalForm (e 2) u = 0 := by
    change inner ℝ (cylinderHorizontalProjection (e 2)) (cylinderHorizontalProjection u) = 0
    rw [hP, inner_zero_left]
  have hH2 : cylinderHorizontalForm u u = 1 := by
    have h := congrArg (fun B : MetricCoefficient 3 => B u u)
      cylinderHorizontalForm_add_vertical
    change cylinderHorizontalForm u u + cylinderHeightCovector u * cylinderHeightCovector u =
      inner ℝ u u at h
    simpa only [hh, zero_mul, add_zero, real_inner_self_eq_norm_sq, hu, one_pow] using h
  have hheight : cylinderHeightCovector (e 2) = 1 := by
    rw [cylinderHeightCovector_basis]
    rfl
  unfold collarJetGram
  change evolvingCylinderModelField 0 0 (e 2) (e 2) *
      evolvingCylinderModelField 0 0 u u -
        (evolvingCylinderModelField 0 0 (e 2) u) ^ 2 = _
  rw [evolvingCylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    hH0, hH1, hH2, hh, hheight]
  norm_num

theorem cylinderModelJet_axialCurvature (u : E) :
    jetCurvature (evolvingCylinderModelJet 0) (e 2) u (e 2) u = 0 := by
  have hP : (cylinderEuclideanEquiv (e 2)).1 = 0 := by
    rw [cylinderEuclideanEquiv_basis]
    rfl
  rw [jetCurvature_evolvingCylinderModelJet]
  simp only [cylinderHorizontalForm_apply, hP, inner_zero_left, zero_mul, sub_self, mul_zero]

theorem exists_cylinder_axial_jet_tolerance {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ J : MetricTwoJet 3,
      ‖J - evolvingCylinderModelJet 0‖ ≤ delta → ∀ u : E,
      ‖u‖ = 1 → cylinderHeightCovector u = 0 →
        0 < collarJetGram (e 2) u J ∧
          |jetCurvature J (e 2) u (e 2) u| < epsilon * collarJetGram (e 2) u J := by
  let K := Metric.sphere (0 : E) 1 ∩ {u | cylinderHeightCovector u = 0}
  have hK : IsCompact K := (isCompact_sphere (0 : E) 1).inter_right
    (isClosed_eq cylinderHeightCovector.continuous continuous_const)
  have hnear : ∀ᶠ J in 𝓝 (evolvingCylinderModelJet 0), ∀ u ∈ K,
      0 < collarJetGram (e 2) u J ∧
        |jetCurvature J (e 2) u (e 2) u| < epsilon * collarJetGram (e 2) u J := by
    apply hK.eventually_forall_of_forall_eventually
    intro u hu
    have hunorm : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu.1
    have hgram := cylinderModelJet_axialGram hunorm hu.2
    have hG : ContinuousAt (fun p : MetricTwoJet 3 × E => collarJetGram (e 2) p.2 p.1)
        (evolvingCylinderModelJet 0, u) := by
      unfold collarJetGram
      fun_prop
    have hR : ContinuousAt (fun p : MetricTwoJet 3 × E =>
        jetCurvature p.1 (e 2) p.2 (e 2) p.2) (evolvingCylinderModelJet 0, u) :=
      continuousAt_jetCurvature_family continuousAt_fst
        (evolvingCylinderModelJet_isInvertible (by norm_num))
        continuousAt_const continuousAt_snd continuousAt_const continuousAt_snd
    have hgpos : 0 < collarJetGram (e 2) u (evolvingCylinderModelJet 0) := by
      rw [hgram]; norm_num
    have hmpos : 0 < epsilon * collarJetGram (e 2) u (evolvingCylinderModelJet 0) -
        |jetCurvature (evolvingCylinderModelJet 0) (e 2) u (e 2) u| := by
      rw [hgram, cylinderModelJet_axialCurvature, abs_zero, sub_zero]
      positivity
    filter_upwards [hG.eventually (lt_mem_nhds hgpos),
      ((continuousAt_const.mul hG).sub hR.abs).eventually (lt_mem_nhds hmpos)] with p hp hq
    exact ⟨hp, sub_pos.mp hq⟩
  obtain ⟨delta, hdelta, hinside⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨delta / 2, half_pos hdelta, ?_⟩
  intro J hJ u hu hh
  apply hinside (show J ∈ Metric.ball (evolvingCylinderModelJet 0) delta from ?_)
    u ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using hu, hh⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hJ.trans_lt (half_lt_self hdelta)

theorem exists_roundCylinder_axial_tolerance {k : ℝ} (hk : 0 < k) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon ≤ epsilon0 → ∀ B : RoundCylinderTwoTensor,
      RoundCylinderClose epsilon 0 B → ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ u : E,
      ‖u‖ = 1 → cylinderHeightCovector u = 0 →
        let J := metricTwoJet (centeredCylinderMetric B z.1 z.2) 0
        0 < collarJetGram (e 2) u J ∧
          |jetCurvature J (e 2) u (e 2) u| < k * collarJetGram (e 2) u J := by
  obtain ⟨delta, hdelta, hmargin⟩ := exists_cylinder_axial_jet_tolerance hk
  refine ⟨min (1 / 2) (delta / 810), lt_min (by norm_num) (by positivity), ?_⟩
  intro epsilon hepsilon hsmall B hB z hz u hu hh
  have hhalf := hsmall.trans (min_le_left _ _)
  have hdelta' := hsmall.trans (min_le_right _ _)
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_ofNat, inv_eq_one_div, le_div_iff₀ hepsilon]
    linarith only [hhalf]
  apply hmargin _ _ u hu hh
  exact (evolving_roundCylinderClose_twoJet_error hepsilon le_rfl zero_lt_one hB
    horder z hz).trans (by linarith only [hdelta'])

end PoincareConjecture.M44
