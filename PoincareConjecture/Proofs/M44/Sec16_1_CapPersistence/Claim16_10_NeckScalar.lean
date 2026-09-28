import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderCurvature
import PoincareConjecture.Proofs.M36.CenteredNeckMetric
import PoincareConjecture.Proofs.M01.NormalizationCurvature
import PoincareConjecture.Proofs.M13.ContractionTransport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance neckScalarCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance neckScalarCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance neckScalarTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance neckScalarTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace




theorem exists_roundCylinder_scalar_lower_cutoff :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon ≤ epsilon0 → ∀ B : RoundCylinderTwoTensor,
      RoundCylinderClose epsilon 0 B → ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        (1 / 2 : ℝ) < jetScalarCurvature
          (metricTwoJet (centeredCylinderMetric B z.1 z.2) 0) := by
  have hmodel : (1 / 2 : ℝ) < jetScalarCurvature (evolvingCylinderModelJet 0) := by
    rw [jetScalarCurvature_evolvingCylinderModelJet zero_lt_one]
    norm_num
  have hnear := (contDiffAt_jetScalarCurvature
    (evolvingCylinderModelJet_isInvertible zero_lt_one)).continuousAt.eventually
      (lt_mem_nhds hmodel)
  obtain ⟨d, hd, hinside⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min (1 / 2) (d / 1620), lt_min (by norm_num) (by positivity), ?_⟩
  intro epsilon hepsilon hsmall B hB z hz
  have hhalf := hsmall.trans (min_le_left _ _)
  have hdelta := hsmall.trans (min_le_right _ _)
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_ofNat, inv_eq_one_div, le_div_iff₀ hepsilon]
    linarith only [hhalf]
  apply hinside
  rw [Metric.mem_ball, dist_eq_norm]
  exact (evolving_roundCylinderClose_twoJet_error hepsilon le_rfl zero_lt_one hB
    horder z hz).trans_lt (by linarith)




theorem exists_neck_scalar_ratio_cutoff :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ x ∈ N.carrier,
        N.connection.scalarCurvature N.center < 2 * N.connection.scalarCurvature x := by
  obtain ⟨epsilon0, hepsilon0, hbound⟩ := exists_roundCylinder_scalar_lower_cutoff
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro M _ _ _ _ g N hsmall x hx
  let z := N.coordinate_inverse x
  have hz := (N.coordinate_inverse_mem x hx).2
  have hzero := zero_mem_centeredNeckDomain N hz
  let f := centeredNeckLift N z.1 z.2
  have hcoeff : (normalizedNeckMetric N).pullbackCoefficients f =ᶠ[𝓝 (0 : E)]
      centeredCylinderMetric (fun q v w => normalizedNeckForm N q v w) z.1 z.2 :=
    eventually_of_mem ((centeredNeckDomain_isOpen N z.2).mem_nhds hzero)
      (fun _ hp => normalizedNeckMetric_pullbackCoefficients N z.1 z.2 hp)
  have htwo : metricTwoJet ((normalizedNeckMetric N).pullbackCoefficients f) 0 =
      metricTwoJet (centeredCylinderMetric
        (fun q v w => normalizedNeckForm N q v w) z.1 z.2) 0 := by
    simp only [metricTwoJet, hcoeff.eq_of_nhds, hcoeff.fderiv_eq,
      (hcoeff.fderiv (𝕜 := ℝ)).fderiv_eq]
  have hscalar := hbound N.epsilon N.epsilon_pos hsmall
    (fun q v w => normalizedNeckForm N q v w) N.metric_comparison.close z hz
  rw [← htwo, jetScalarCurvature_pullbackCoefficients (normalizedNeckMetric N)
    (normalizedNeckConnection N) (centeredNeckDomain_isOpen N z.2)
    (fun p hp => (centeredNeckLift_contMDiffAt N z.1 z.2 hp).contMDiffWithinAt)
    (fun p hp => centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hp) hzero] at hscalar
  have hfx : f 0 = x := (centeredNeckLift_zero N z.1 z.2).trans
    (neck_coordinate_inverse N hx)
  change (1 / 2 : ℝ) < (normalizedNeckConnection N).scalarCurvature (f 0) at hscalar
  rw [hfx] at hscalar
  have hhom : MetricHomothety g (normalizedNeckMetric N) (Diffeomorph.refl (𝓡 3) M ∞)
      (N.connection.scalarCurvature N.center) := by
    intro y v w
    simp only [Diffeomorph.coe_refl, mfderiv_id]
    rfl
  have hscale := M13.homothety_scalarCurvature_eq g (normalizedNeckMetric N)
    (Diffeomorph.refl (𝓡 3) M ∞) _ N.scalar_center_pos hhom
    N.connection (normalizedNeckConnection N) x
  change (normalizedNeckConnection N).scalarCurvature x =
    N.connection.scalarCurvature x / N.connection.scalarCurvature N.center at hscale
  rw [hscale] at hscalar
  have hmul := (lt_div_iff₀ N.scalar_center_pos).mp hscalar
  linarith

end PoincareConjecture.M44
