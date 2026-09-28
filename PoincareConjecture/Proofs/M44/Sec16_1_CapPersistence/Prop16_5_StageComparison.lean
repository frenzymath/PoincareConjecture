import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_ControlledStages
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderSampleAgreement
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJetsSequence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_TwoJetModulus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance stageComparisonCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance stageComparisonCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance stageComparisonTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance stageComparisonTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

variable {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
  {start rNext A eta theta Rinner : ℝ} {cutoffs : ℕ → ℝ}
  {X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) Rinner}

theorem eventually_stage_spatial_jets
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {R0 T K c : ℝ} (hstage : CapSequenceStage X R0 T K)
    (heta : Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0))
    (hlim : Tendsto (fun n => (X n).sample.lifetime) atTop (𝓝 c))
    (hT : 0 < T) (hK : 0 < K) (htheta : 0 < theta) (htheta1 : theta < 1)
    (hc : 0 ≤ c) (hctheta : c ≤ theta) (m : ℕ) {C : Set E} (hC : IsCompact C)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    ∀ᶠ n in atTop,
      ∀ D : CylinderCompactnessSample setup.standard_initial (X n).data.flow
        (X n).data.time (X n).data.is_surgery (X n).data.cap,
      D.comparison.map = (X n).sample.comparison.map →
      ∀ t ∈ Ico (0 : ℝ) (min (X n).sample.lifetime T), t < D.lifetime →
      ∀ x ∈ C, x ∈ D.chart.source →
        ‖iteratedFDeriv ℝ m (fun y => D.coefficients (t, y)) x -
          iteratedFDeriv ℝ m (standard.flow.metric t).euclideanCoefficients x‖ < accuracy := by
  classical
  by_contra hnot
  obtain ⟨sigma, hsigma, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hnot)
  obtain ⟨tau, htau, ⟨S⟩⟩ := (hstage.subsequence hsigma).diagonal
  let D (n : ℕ) := (S n).restricted hT
  have hmono : StrictMono (sigma ∘ tau) := hsigma.comp htau
  have hR : Tendsto (fun n => (D n).radius) atTop atTop := by
    have heq : (fun n => (D n).radius) = (fun n : ℕ => R0 + (n : ℝ) + 1) :=
      funext fun n => (S n).radius_eq
    rw [heq]
    exact tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ R0 tendsto_natCast_atTop_atTop)
  have hetaD : Tendsto (fun n => (D n).eta) atTop (𝓝 0) := by
    have heq : (fun n => (D n).eta) = (fun n => (X (sigma (tau n))).sample.eta) :=
      funext fun n => (S n).eta_eq
    rw [heq]
    exact heta.comp hmono.tendsto_atTop
  have hlifeD : Tendsto (fun n => (D n).lifetime) atTop (𝓝 (min c T)) :=
    (hlim.comp hmono.tendsto_atTop).min tendsto_const_nhds
  have hlifeTheta (n : ℕ) : (D n).lifetime ≤ theta :=
    (min_le_left _ _).trans ((X (sigma (tau n))).sample.lifetime_le.trans
      (X (sigma (tau n))).data.assignedDuration_le)
  have hcurvD : ∀ᶠ n in atTop, ∀ t ∈ Ico (0 : ℝ) (D n).lifetime, ∀ y,
      ((D n).ordinary.flow.connection t).curvatureTensorNorm y ≤ K :=
    Eventually.of_forall fun n => (S n).curvature
  have hclose := eventually_cylinder_standard_spatial_jets P standard unique D hR hetaD
    htheta htheta1 (le_min hc hT.le) ((min_le_left _ _).trans hctheta)
    hlifeTheta hlifeD hK hcurvD m hC accuracy haccuracy
  have hsource := eventually_cylinder_compact_subset_source D hR hC
  obtain ⟨n, hcloseN, hsourceN⟩ := (hclose.and hsource).exists
  apply hbad (tau n)
  intro other hmap t ht htother x hx hxother
  have hmapD : other.comparison.map = (D n).comparison.map :=
    hmap.trans (S n).comparison_eq.symm
  rw [other.spatial_jet_eq_of_comparison_map_eq (D n) hmapD
    ⟨ht.1, htother⟩ ht hxother (hsourceN hx) m]
  exact hcloseN t ht x hx

theorem eventually_stage_finite_spatial_jets
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {R0 T K c : ℝ} (hstage : CapSequenceStage X R0 T K)
    (heta : Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0))
    (hlim : Tendsto (fun n => (X n).sample.lifetime) atTop (𝓝 c))
    (hT : 0 < T) (hK : 0 < K) (htheta : 0 < theta) (htheta1 : theta < 1)
    (hc : 0 ≤ c) (hctheta : c ≤ theta) (m : ℕ) {C : Set E} (hC : IsCompact C)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    ∀ᶠ n in atTop,
      ∀ D : CylinderCompactnessSample setup.standard_initial (X n).data.flow
        (X n).data.time (X n).data.is_surgery (X n).data.cap,
      D.comparison.map = (X n).sample.comparison.map →
      ∀ t ∈ Ico (0 : ℝ) (min (X n).sample.lifetime T), t < D.lifetime →
      ∀ x ∈ C, x ∈ D.chart.source → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (fun y => D.coefficients (t, y)) x -
          iteratedFDeriv ℝ j (standard.flow.metric t).euclideanCoefficients x‖ < accuracy := by
  have hall : ∀ᶠ n in atTop, ∀ j : Fin (m + 1),
      ∀ D : CylinderCompactnessSample setup.standard_initial (X n).data.flow
        (X n).data.time (X n).data.is_surgery (X n).data.cap,
      D.comparison.map = (X n).sample.comparison.map →
      ∀ t ∈ Ico (0 : ℝ) (min (X n).sample.lifetime T), t < D.lifetime →
      ∀ x ∈ C, x ∈ D.chart.source →
        ‖iteratedFDeriv ℝ j.val (fun y => D.coefficients (t, y)) x -
          iteratedFDeriv ℝ j.val (standard.flow.metric t).euclideanCoefficients x‖ < accuracy :=
    Filter.eventually_all.mpr fun j => eventually_stage_spatial_jets P standard unique
      hstage heta hlim hT hK htheta htheta1 hc hctheta j.val hC haccuracy
  filter_upwards [hall] with n hn
  intro D hmap t ht htlife x hx hxD j hj
  exact hn ⟨j, Nat.lt_succ_of_le hj⟩ D hmap t ht htlife x hx hxD

theorem eventually_stage_twoJet_comparison
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {R0 T K c : ℝ} (hstage : CapSequenceStage X R0 T K)
    (heta : Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0))
    (hlim : Tendsto (fun n => (X n).sample.lifetime) atTop (𝓝 c))
    (hT : 0 < T) (hK : 0 < K) (htheta : 0 < theta) (htheta1 : theta < 1)
    (hc : 0 ≤ c) (hctheta : c ≤ theta) {C : Set E} (hC : IsCompact C)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    ∀ᶠ n in atTop,
      ∀ D : CylinderCompactnessSample setup.standard_initial (X n).data.flow
        (X n).data.time (X n).data.is_surgery (X n).data.cap,
      D.comparison.map = (X n).sample.comparison.map →
      ∀ t ∈ Ico (0 : ℝ) (min (X n).sample.lifetime T), t < D.lifetime →
      ∀ x ∈ C, x ∈ D.chart.source →
        ‖metricTwoJet (fun y => D.coefficients (t, y)) x -
          metricTwoJet (standard.flow.metric t).euclideanCoefficients x‖ ≤ accuracy := by
  filter_upwards [eventually_stage_finite_spatial_jets P standard unique hstage heta hlim
    hT hK htheta htheta1 hc hctheta 2 hC haccuracy] with n hn
  intro D hmap t ht htlife x hx hxD
  exact norm_metricTwoJet_sub_le _ _ x (fun j hj => (hn D hmap t ht htlife x hx hxD j hj).le)

end PoincareConjecture.M44
