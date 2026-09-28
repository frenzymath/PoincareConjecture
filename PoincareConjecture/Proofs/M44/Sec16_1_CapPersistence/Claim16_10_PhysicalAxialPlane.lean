import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_AxialJetMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_PullbackPlane
import PoincareConjecture.Proofs.M36.CenteredNeckMetric
import PoincareConjecture.Proofs.M01.NormalizationCurvature











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance axialPlaneCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance axialPlaneCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace




theorem exists_normalized_neck_axial_cutoff {k : ℝ} (hk : 0 < k) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ u : E, ‖u‖ = 1 → cylinderHeightCovector u = 0 →
        let f := centeredNeckLift N z.1 z.2
        let L := mfderiv (𝓡 3) (𝓡 3) f 0
        let h := normalizedNeckMetric N
        0 < h.inner (f 0) (L (e 2)) (L (e 2)) * h.inner (f 0) (L u) (L u) -
          (h.inner (f 0) (L (e 2)) (L u)) ^ 2 ∧
          |(normalizedNeckConnection N).sectionalCurvature (f 0) (L (e 2)) (L u)| < k := by
  obtain ⟨epsilon0, hepsilon0, hbound⟩ := exists_roundCylinder_axial_tolerance hk
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro M _ _ _ _ g N hsmall z hz u hu hh
  let f := centeredNeckLift N z.1 z.2
  let h := normalizedNeckMetric N
  let D := normalizedNeckConnection N
  have hzero := zero_mem_centeredNeckDomain N hz
  have hcoeff : h.pullbackCoefficients f =ᶠ[𝓝 (0 : E)]
      centeredCylinderMetric (fun q v w => normalizedNeckForm N q v w) z.1 z.2 :=
    eventually_of_mem ((centeredNeckDomain_isOpen N z.2).mem_nhds hzero)
      (fun _ hp => normalizedNeckMetric_pullbackCoefficients N z.1 z.2 hp)
  have htwo : metricTwoJet (h.pullbackCoefficients f) 0 =
      metricTwoJet (centeredCylinderMetric
        (fun q v w => normalizedNeckForm N q v w) z.1 z.2) 0 := by
    simp only [metricTwoJet, hcoeff.eq_of_nhds, hcoeff.fderiv_eq,
      (hcoeff.fderiv (𝕜 := ℝ)).fderiv_eq]
  obtain ⟨hgram, hcurv⟩ := hbound N.epsilon N.epsilon_pos hsmall
    (fun q v w => normalizedNeckForm N q v w) N.metric_comparison.close z hz u hu hh
  rw [← htwo] at hgram hcurv
  have hR := jetCurvature_pullbackCoefficients h D (centeredNeckDomain_isOpen N z.2)
    (fun p hp => (centeredNeckLift_contMDiffAt N z.1 z.2 hp).contMDiffWithinAt)
    (fun p hp => centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hp)
    hzero (e 2) u (e 2) u
  refine ⟨hgram, ?_⟩
  change |D.sectionalCurvature (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 (e 2))
    (mfderiv (𝓡 3) (𝓡 3) f 0 u)| < k
  unfold LeviCivitaData.sectionalCurvature
  rw [← hR, abs_div]
  change |jetCurvature (metricTwoJet (h.pullbackCoefficients f) 0) (e 2) u (e 2) u| /
    |collarJetGram (e 2) u (metricTwoJet (h.pullbackCoefficients f) 0)| < k
  rw [abs_of_pos hgram]
  exact (div_lt_iff₀ hgram).mpr hcurv




theorem normalizedNeck_sectional
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (x : M) (u v : TangentSpace (𝓡 3) x) :
    (normalizedNeckConnection N).sectionalCurvature x u v =
      N.connection.sectionalCurvature x u v / N.connection.scalarCurvature N.center := by
  unfold LeviCivitaData.sectionalCurvature
  rw [show (normalizedNeckConnection N).curvatureTensor x u v u v =
    N.connection.scalarCurvature N.center * N.connection.curvatureTensor x u v u v from
      m01RescaledMetric_curvatureTensor g N.connection _ N.scalar_center_pos x u v u v]
  simp only [normalizedNeckMetric, m01RescaledMetric_inner]
  let Q := N.connection.scalarCurvature N.center
  change Q * N.connection.curvatureTensor x u v u v /
    ((Q * g.inner x u u) * (Q * g.inner x v v) - (Q * g.inner x u v) ^ 2) = _
  rw [show (Q * g.inner x u u) * (Q * g.inner x v v) - (Q * g.inner x u v) ^ 2 =
    Q * (Q * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) by ring]
  rw [mul_div_mul_left _ _ N.scalar_center_pos.ne', div_mul_eq_div_div, div_right_comm]




theorem exists_physical_neck_axial_cutoff {k : ℝ} (hk : 0 < k) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ u : E, ‖u‖ = 1 → cylinderHeightCovector u = 0 →
        let f := centeredNeckLift N z.1 z.2
        let L := mfderiv (𝓡 3) (𝓡 3) f 0
        |N.connection.sectionalCurvature (f 0) (L (e 2)) (L u)| <
          k * N.connection.scalarCurvature N.center := by
  obtain ⟨epsilon0, hepsilon0, hbound⟩ := exists_normalized_neck_axial_cutoff hk
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro M _ _ _ _ g N hsmall z hz u hu hh
  have h := (hbound N hsmall z hz u hu hh).2
  rw [normalizedNeck_sectional, abs_div, abs_of_pos N.scalar_center_pos] at h
  exact (div_lt_iff₀ N.scalar_center_pos).mp h

end PoincareConjecture.M44
