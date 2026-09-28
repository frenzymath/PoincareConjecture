import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_GlobalStandardCollar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialExactCutoff
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_SmallHeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

theorem exists_initial_cylinder_cutoff (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    (K : MetricSurgeryConstants) {epsilon C r A : ℝ}
    (hepsilon : 0 < epsilon) (hC : 0 < C) (hr : 0 < r) (hA : 0 < A) :
    ∃ R0 tau M : ℝ, ∃ x u v : E,
      A < R0 ∧ 2 < R0 ∧ 0 < tau ∧ 1 ≤ M ∧
      ∀ R : ℝ, R0 ≤ R → ∃ eta deltaBar : ℝ,
      0 < eta ∧ R < eta⁻¹ ∧ 0 < deltaBar ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 → F.local_constants = K →
      F.parameters.epsilon = epsilon → F.parameters.C = C →
      ∀ (a : ℝ) (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier],
      F.parameters.delta a ≤ deltaBar → ∀ i : Fin (F.event a ha).cap_count,
      ∃ Q : SurgeryCapClose F.standard_initial
        ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
        ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta,
      ((F.event a ha).necks i).neck.epsilon ≤ F.local_constants.comparison_delta eta ∧
      ∀ B : ℝ, 0 < B →
      ∀ e : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2) (Ico 0 B)
        ((F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R)),
      (∀ h y, y ∈ (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R) →
        HEq (e.forward 0 h y) y) →
      SurgeryCanonicalOn F (Ico a (a + B / ((F.parameters.h a)⁻¹ ^ 2))) r →
      SurgeryFlowPinched F →
      ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞,
        f.source = F.standard_initial.metric.ball 0 R ∧
        f.target = (F.metric a).ball ((F.event a ha).caps i).tip (F.parameters.h a * R) ∧
        (∀ y, f y = (F.event a ha).local_embed i (Q.map y)) ∧
        ∃ G : CylinderRicciFlow e f,
        ∃ p : (⟨f.target, f.open_target⟩ : TopologicalSpace.Opens (F.slice a).carrier),
        ∀ T : ℝ, 0 < T → T < B → T ≤ tau →
          (∀ s ∈ Icc (0 : ℝ) T,
            metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x ∈
              collarJetRegion C u v) ∧
          (∀ s ∈ Icc (0 : ℝ) T, ∀ y,
            (G.flow.connection s).scalarCurvature y ≤ 2 * M ∧
            (G.flow.connection s).curvatureTensorNorm y ≤ 13 * max (2 * M) (Real.exp 4)) := by
  obtain ⟨x, u, v, _hcompact, hcollar⟩ :=
    exists_global_standard_collar standard hC (theta := 0) le_rfl zero_lt_one
  have hJ := hcollar 0 ⟨le_rfl, le_rfl⟩
  change metricTwoJet (standard.flow.base.flow.metric 0).euclideanCoefficients x ∈
    collarJetRegion C u v at hJ
  rw [standard.flow.base.initial_metric] at hJ
  let R0 := |M36.radialArclength g0 ‖x‖| + A + 4
  have hRA : A < R0 := by
    dsimp [R0]
    linarith only [abs_nonneg (M36.radialArclength g0 ‖x‖)]
  have hR0 : 2 < R0 := by
    dsimp [R0]
    linarith only [abs_nonneg (M36.radialArclength g0 ‖x‖), hA]
  have hx : x ∈ g0.metric.ball 0 (R0 - 2) := by
    change g0.metric.edist 0 x < ENNReal.ofReal (R0 - 2)
    rw [M36.standard_edist_zero, ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R0 - 2)]
    dsimp only [R0]
    linarith only [le_abs_self (M36.radialArclength g0 ‖x‖), hA]
  obtain ⟨d, tau, M, hd, htau, hM, hbound⟩ :=
    exists_initial_cylinder_bound P g0 standard.initial_estimate C x u v hJ hR0 hx
  obtain ⟨dh, hdh, hheight⟩ := exists_surgery_normalization_cutoff hepsilon hr
  refine ⟨R0, tau, M, x, u, v, hRA, hR0, htau, hM, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  let eta := min (d / 2) (1 / (2 * (R + 1)))
  have heta : 0 < eta := lt_min (half_pos hd) (by positivity)
  have hetad : eta ≤ d := (min_le_left _ _).trans (by linarith)
  have hfit : R < eta⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ heta]
    have hle : eta * (2 * (R + 1)) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * (R + 1))).mp (min_le_right _ _)
    nlinarith
  obtain ⟨dc, hdc, hcomparison⟩ := exists_initial_cap_exact_comparison_cutoff.{u} g0 K heta
  refine ⟨eta, min dc dh, heta, hfit, lt_min hdc hdh, ?_⟩
  intro F hg0 hK heps hconstant a ha _ hdelta i
  have ha0 := F.time_domain_nonnegative (F.surgery_times_subset ha)
  obtain ⟨hsmall, hthreshold⟩ := hheight F.parameters heps a ha0
    (hdelta.trans (min_le_right _ _))
  obtain ⟨Q, hlink, hballs⟩ := hcomparison F hg0 hK a ha
    (hdelta.trans (min_le_left _ _)) i
  refine ⟨Q, hlink, ?_⟩
  intro B hB e hinitial hcanonical hpinch
  have hq : F.parameters.h a ^ 2 * (r⁻¹ ^ 2) ≤ 1 := by
    simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hthreshold
  apply hbound F hg0 a ha i hR hfit hB hsmall hq Q hetad hballs e hinitial _ hpinch
  intro s hs y hy
  rw [← hconstant]
  apply hcanonical _ _ (e.time_subset (mem_image_of_mem _ hs)) y hy
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hs.1 e.scale_pos.le)
  · linarith only [(div_lt_div_iff_of_pos_right e.scale_pos).mpr hs.2]

end PoincareConjecture.M44
