import PoincareConjecture.Proofs.M47.BlowupControlsCapCoefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

noncomputable local instance capBirthCoefficientNorm : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capBirthCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance capBirthTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance capBirthTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace



theorem exists_actualCap_birth_metric_bound {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) (hA : 0 < A) :
    ∃ Z eta0 : ℝ, 0 < Z ∧ 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      ∀ G : M44.CylinderRicciFlow e (capInitialPartialDiffeomorph initial),
      ∀ p : (⟨(capInitialPartialDiffeomorph initial).target,
        (capInitialPartialDiffeomorph initial).open_target⟩ : Opens (F.slice t).carrier),
      0 ∈ J → ∀ x ∈ F.standard_initial.metric.ball 0 A,
        ‖(G.flow.metric 0).pullbackCoefficients
          (M44.targetChart (capInitialPartialDiffeomorph initial) p) x‖ ≤ Z := by
  obtain ⟨C, hC, htwo⟩ := exists_actualCap_twoJet_bound.{u} standard htheta hA
  obtain ⟨alpha, _halpha, B, hmodel⟩ := M44.exists_standard_family_ellipticity_jet_bound
    standard.flow.base (by simpa only [standard.lifetime_one] using htheta)
    (M36.standard_closed_ball_compact g0 hA.le) 0
  let Z : ℝ := max B 0 + 2
  let eta0 : ℝ := min (1 / 2) (1 / C)
  have hZ : 0 < Z := by dsimp [Z]; linarith only [le_max_right B 0]
  have heta0 : 0 < eta0 := lt_min (by norm_num) (one_div_pos.mpr hC)
  refine ⟨Z, eta0, hZ, heta0, min_le_left _ _, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaSmall comparison G p hzero x hx
  have hetaHalf : eta ≤ 1 / 2 := hetaSmall.trans (min_le_left _ _)
  have hCeta : C * eta ≤ 1 := by
    have := (le_div_iff₀ hC).mp (hetaSmall.trans (min_le_right _ _))
    nlinarith
  have hnear := (htwo F hinitial S hS t hT hn i J U e initial eta heta hetaHalf comparison
    0 hzero htheta0 x hx).trans hCeta
  have hmap : (capInitialPartialDiffeomorph initial).target ⊆ U := by
    change initial.chart '' F.standard_initial.metric.ball 0 A ⊆ U
    rw [comparison.choose_spec.2.2.2.1]
  rw [← cap_ordinary_twoJet_eq e initial G hmap p 0 hzero hx] at hnear
  have hclosed : x ∈ {y | g0.metric.edist 0 y ≤ ENNReal.ofReal A} := by
    rw [← hinitial]
    change F.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal A
    change F.standard_initial.metric.edist 0 x < ENNReal.ofReal A at hx
    exact le_of_lt hx
  have hb : ‖(S.metric 0).euclideanCoefficients x‖ ≤ B := by
    cases hinitial
    cases hS
    simpa only [MaximalStandardCapFlow.metric, norm_iteratedFDeriv_zero] using
      (hmodel 0 ⟨le_rfl, htheta0⟩ x hclosed).2 0 le_rfl
  have hdiff : ‖(G.flow.metric 0).pullbackCoefficients
      (M44.targetChart (capInitialPartialDiffeomorph initial) p) x -
        (S.metric 0).euclideanCoefficients x‖ ≤ 1 :=
    (norm_fst_le _).trans hnear
  calc
    _ ≤ ‖(G.flow.metric 0).pullbackCoefficients
        (M44.targetChart (capInitialPartialDiffeomorph initial) p) x -
          (S.metric 0).euclideanCoefficients x‖ +
        ‖(S.metric 0).euclideanCoefficients x‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + B := add_le_add hdiff hb
    _ ≤ Z := by dsimp [Z]; linarith only [le_max_left B 0]

end PoincareConjecture.M47
