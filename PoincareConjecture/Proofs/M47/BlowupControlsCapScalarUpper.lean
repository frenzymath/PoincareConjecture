import PoincareConjecture.Proofs.M47.BlowupControlsCapJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_ScalarComparisonModel










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

noncomputable local instance capUpperCoefficientNorm : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capUpperCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance capUpperTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance capUpperTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace



theorem exists_actualCap_scalar_upper {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 < A →
      ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      0 < F.parameters.h t → ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ U, (F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward s hs x) ≤ K := by
  obtain ⟨M, hM, hmodel⟩ := M44.exists_global_standard_scalar_bound standard htheta0 htheta
  refine ⟨M + 1, by linarith, ?_⟩
  intro A hA
  obtain ⟨C, hC, htwo⟩ := exists_actualCap_twoJet_bound.{u} standard htheta hA
  obtain ⟨delta, hdelta, hmargin⟩ := M44.exists_standard_scalar_comparison_tolerance
    standard htheta hmodel (M36.standard_closed_ball_compact g0 hA.le)
  let eta0 : ℝ := min (1 / 2) (delta / C)
  have heta0 : 0 < eta0 := lt_min (by norm_num) (div_pos hdelta hC)
  refine ⟨eta0, heta0, min_le_left _ _, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaSmall comparison hh s hs hst x hx
  have hetaHalf : eta ≤ 1 / 2 := hetaSmall.trans (min_le_left _ _)
  have hCeta : C * eta ≤ delta := by
    have := (le_div_iff₀ hC).mp (hetaSmall.trans (min_le_right _ _))
    nlinarith
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  obtain ⟨z, hz, rfl⟩ := himage.symm ▸ hx
  have hnear := (htwo F hinitial S hS t hT hn i J U e initial eta heta hetaHalf comparison
    s hs hst z hz).trans hCeta
  have hclosed : z ∈ {y | g0.metric.edist 0 y ≤ ENNReal.ofReal A} := by
    rw [← hinitial]
    change F.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal A
    change F.standard_initial.metric.edist 0 z < ENNReal.ofReal A at hz
    exact le_of_lt hz
  have htime : s ∈ Icc 0 theta := ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  have hscalar : M44.jetScalarCurvature
      (metricTwoJet (capComparisonCoefficients e initial.chart s hs) z) < M + 1 := by
    cases hinitial
    cases hS
    exact hmargin s htime z hclosed _ hnear
  rw [capComparison_scalar_readout e initial comparison hh s hs hz] at hscalar
  exact hscalar.le

end PoincareConjecture.M47
