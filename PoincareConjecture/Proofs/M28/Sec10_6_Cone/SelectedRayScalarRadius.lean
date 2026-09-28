import PoincareConjecture.Proofs.M28.Mathlib.PositiveChordScale
import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRay
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedSphereRayCrossing
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedNeckIntrinsicBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}

theorem exists_selected_ray_scalar_radius_upper
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (D : LeviCivitaData g)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        D.scalarCurvature y ≤ 2 * D.scalarCurvature z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D.scalarCurvature x)
    (hpositive : ∀ x : U, 0 < D.scalarCurvature x)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ E : UniformSpace.Completion U,
      E ∉ range ((↑) : U → UniformSpace.Completion U) →
      ∀ (alpha : ℝ) (P Q : MetricEndRay E alpha) (K : ℝ), 0 < K →
      Tendsto (fun z : ℝ × ℝ =>
        chordDefect (fun s t => dist (P.point s) (Q.point t)) z.1 z.2)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 K) →
      (∀ s ∈ Ioc (0 : ℝ) P.length, (3 / 4 : ℝ) ≤ (A.inverse (P.point s)).2) →
      (∀ t ∈ Ioc (0 : ℝ) Q.length, (3 / 4 : ℝ) ≤ (A.inverse (Q.point t)).2) →
      ∃ eta B : ℝ, 0 < eta ∧ eta ≤ P.length ∧ 0 < B ∧
        ∀ s ∈ Ioo (0 : ℝ) eta, D.scalarCurvature (P.point s) * s ^ 2 ≤ B := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  intro E houtside alpha P Q K hK hlimit hPlower hQlower
  let kappa : ℝ := min (K / 2) 1
  have hkappa : 0 < kappa := lt_min (half_pos hK) zero_lt_one
  have hkappa1 : kappa ≤ 1 := min_le_right _ _
  have hkappaK : kappa < K := (min_le_left _ _).trans_lt (half_lt_self hK)
  obtain ⟨etaP, hetaP, etaQ, hetaQ, hdefect⟩ :=
    exists_positive_rectangle_of_joint_limit hlimit hkappaK
  let B0 : ℝ := min (Q.length / 2) (etaQ / 2)
  have hB0 : 0 < B0 := lt_min (half_pos Q.length_pos) (half_pos hetaQ)
  have hB0Q : B0 < Q.length := (min_le_left _ _).trans_lt (half_lt_self Q.length_pos)
  have hB0eta : B0 < etaQ := (min_le_right _ _).trans_lt (half_lt_self hetaQ)
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hQheight : (A.inverse (Q.point B0)).2 < 1 :=
    (A.inverse_mem (Q.point B0) (hUV (Q.point B0).property)).2.2
  obtain ⟨c, hcabove, hc1⟩ := exists_between
    (max_lt (by norm_num : (1 / 2 : ℝ) < 1) hQheight)
  have hc : 1 / 2 < c := (le_max_left _ _).trans_lt hcabove
  have hstart : (A.inverse (Q.point B0)).2 < c := (le_max_right _ _).trans_lt hcabove
  obtain ⟨d, _hdhalf, hd1, hwhole⟩ :=
    exists_selected_chain_tail_above_cylinder_level T A D.scalarCurvature
      D.continuous_scalarCurvature.continuousOn hratio hdiverge hc hc1
  obtain ⟨eta0, heta0, hheight⟩ :=
    exists_completion_radius_threshold_for_cylinder_height T A U hU hfinite E houtside d hd1
  let eta : ℝ := min (min etaP eta0) P.length
  have heta : 0 < eta := lt_min (lt_min hetaP heta0) P.length_pos
  have hetaLength : eta ≤ P.length := min_le_right _ _
  let C : ℝ := 2 * T.epsilon⁻¹ + 8 * standardSpherePathCeiling
  have hC : 0 < C := by
    have hepsilon := inv_pos.mpr T.epsilon_pos
    have hL := standardSpherePathCeiling_pos
    dsimp only [C]
    positivity
  refine ⟨eta, 4 * C ^ 2 / kappa, heta, hetaLength, by positivity, ?_⟩
  intro s hs
  have hsP : s ∈ Ioc (0 : ℝ) P.length := ⟨hs.1, hs.2.le.trans hetaLength⟩
  have hsEtaP : s < etaP := hs.2.trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hsEta0 : s < eta0 := hs.2.trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  have hsmall : dist (P.point s : UniformSpace.Completion U) E < eta0 := by
    rw [P.radius s hsP]
    exact hsEta0
  have hhigh := hheight (P.point s) (hPlower s hsP) hsmall
  obtain ⟨i, hpoint⟩ := mem_iUnion.mp (T.carrier_eq_chain_union ▸ hUV (P.point s).property)
  let N : EpsilonNeck g := T.chain.neck i.1
  have hNhigh : N.carrier ⊆ A.tail true c := hwhole i.1 i.2 (P.point s) hpoint hhigh
  have hNU : N.carrier ⊆ (U : Set M) := by
    intro z hz
    have hzread := (A.mem_tail_iff_m28 true (lt_trans (by norm_num) hc) hc1).mp (hNhigh hz)
    rw [hU]
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hzread.1, hc.trans hzread.2⟩
  let gamma : ℝ → U := fun v => Q.point (B0 - v)
  have hparameter (v : ℝ) (hv : v ∈ Ico (0 : ℝ) B0) :
      B0 - v ∈ Ioc (0 : ℝ) Q.length := by
    constructor <;> linarith only [hv.1, hv.2, hB0Q]
  have hgamma : ContinuousOn gamma (Ico (0 : ℝ) B0) :=
    Q.continuousOn_point.comp (continuous_const.sub continuous_id).continuousOn hparameter
  have hgammaLower (v : ℝ) (hv : v ∈ Ico (0 : ℝ) B0) :
      (3 / 4 : ℝ) ≤ (A.inverse (gamma v)).2 := hQlower _ (hparameter v hv)
  have hgammaRadius (v : ℝ) (hv : v ∈ Ico (0 : ℝ) B0) :
      dist (gamma v : UniformSpace.Completion U) E = B0 - v :=
    Q.radius _ (hparameter v hv)
  obtain ⟨v, hv, hcross⟩ := exists_inward_ray_crossing_selected_sphere
    T A U hU hA i.1 i.2 hc hc1 hNhigh hfinite E houtside B0 hB0 gamma
      hgamma hgammaLower hgammaRadius (by simpa only [gamma, sub_zero] using hstart)
  let t : ℝ := B0 - v
  have ht : 0 < t := sub_pos.mpr hv.2
  have htB0 : t < B0 := sub_lt_self B0 hv.1
  have htEta : t < etaQ := htB0.trans hB0eta
  have hcrossN : (Q.point t : M) ∈ N.central_sphere := hcross
  have hcost := intrinsicOpenMetric_edist_neck_to_sphere_le N U hNU hpoint hcrossN
  have hed : (intrinsicOpenMetric g U).edist (P.point s) (Q.point t) =
      ENNReal.ofReal (dist (P.point s) (Q.point t)) := by
    change edist (P.point s) (Q.point t) = _
    exact edist_dist _ _
  have hNepsilon : N.epsilon = T.epsilon := T.chain.epsilon_eq i.1 i.2
  rw [hed, hNepsilon] at hcost
  have hdistance : dist (P.point s) (Q.point t) ≤ C * N.scale :=
    (ENNReal.ofReal_le_ofReal_iff (mul_pos hC N.scale_pos).le).mp hcost
  have hscalar := hratio i.1 i.2 (P.point s) hpoint N.center
    (N.central_sphere_subset N.center_on_central_sphere)
  have hnormal := tube.neck_normalized_scalar_center N D
  have hscaledScalar := mul_le_mul_of_nonneg_right hscalar (sq_nonneg N.scale)
  have hscalarScale : D.scalarCurvature (P.point s) * N.scale ^ 2 ≤ 2 := by
    nlinarith only [hscaledScalar, hnormal]
  have hdefectPair := hdefect s ⟨hs.1, hsEtaP⟩ t ⟨ht, htEta⟩
  change kappa < (dist (P.point s) (Q.point t) ^ 2 - (s - t) ^ 2) / (s * t)
    at hdefectPair
  have hmultiplied := (lt_div_iff₀ (mul_pos hs.1 ht)).mp hdefectPair
  have hchord : (s - t) ^ 2 + kappa * s * t ≤ dist (P.point s) (Q.point t) ^ 2 := by
    nlinarith only [hmultiplied]
  exact scalar_radius_ratio_le_of_chord_lower hkappa hkappa1 dist_nonneg hC.le
    N.scale_pos.le (hpositive (P.point s)).le hchord hdistance hscalarScale

end PoincareConjecture.M28
