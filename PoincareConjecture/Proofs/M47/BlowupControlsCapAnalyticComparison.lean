import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticTolerance
import PoincareConjecture.Proofs.M47.BlowupControlsCapPhysicalAnalytics
import PoincareConjecture.Proofs.M47.BlowupControlsCapRecordedJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds SpacetimeBounds.Bootstrap Proofs.M46

local notation "E" => StandardCapSpace

noncomputable local instance capAnalyticComparisonCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capAnalyticComparisonCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

theorem exists_actualCap_analytic_comparison_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A nu : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hnu : 0 < nu) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      0 < F.parameters.h t →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
      let h := F.parameters.h t
      let D := F.connection (t + s / (h⁻¹ ^ 2))
      let p := e.forward s hs (initial.chart x)
      ‖(h ^ 2 * D.scalarCurvature p,
          h ^ 3 * scalarGradientNorm (F.metric (t + s / (h⁻¹ ^ 2))) D p,
          h ^ 4 * (D.laplacian D.scalarCurvature p + 2 * D.ricciNormSq p)) -
        ((S.connection s).scalarCurvature x,
          scalarGradientNorm (S.metric s) (S.connection s) x,
          (S.connection s).laplacian (S.connection s).scalarCurvature x +
            2 * (S.connection s).ricciNormSq x)‖ ≤ nu := by
  obtain ⟨C, hC, hcoordinate⟩ :=
    exists_actualCap_coordinate_derivative_bound standard htheta hA 4
  obtain ⟨delta, hdelta, hanalytic⟩ := exists_standardCap_analyticJet_tolerance standard.flow
    (by simpa only [standard.lifetime_one] using htheta)
    (M36.standard_closed_ball_compact g0 hA.le) hnu
  refine ⟨min (1 / 5) (delta / C), lt_min (by norm_num) (div_pos hdelta hC), ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta heta0 comparison hh s hs hst x hx
  have hetaOrder : eta ≤ 1 / ((4 : ℝ) + 1) := by
    norm_num
    exact heta0.trans (min_le_left _ _)
  have hcoeff := hcoordinate F hinitial S hS t hT hn i J U e initial eta heta hetaOrder
    comparison s hs hst x hx
  have hjet : ‖spatialJet 4
      (fun z : ℝ × E => capComparisonCoefficients e initial.chart s hs z.2) (0, x) -
      spatialJet 4 (fun z : ℝ × E => (S.metric z.1).euclideanCoefficients z.2)
        (s, x)‖ ≤ C * eta := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le heta.le)).mpr
    intro j
    exact hcoeff j (Nat.le_of_lt_succ j.isLt)
  have hsmall : C * eta ≤ delta := by
    simpa only [mul_comm] using (le_div_iff₀ hC).mp (heta0.trans (min_le_right _ _))
  have hnear := hjet.trans hsmall
  have htime : s ∈ Icc 0 theta := ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  have hclosed : x ∈ {y | g0.metric.edist 0 y ≤ ENNReal.ofReal A} := by
    rw [← hinitial]
    change F.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal A
    change F.standard_initial.metric.edist 0 x < ENNReal.ofReal A at hx
    exact hx.le
  have hread := capComparison_analytic_height_readout e initial comparison hh s hs hx
  cases hinitial
  cases hS
  have h := (hanalytic s htime x hclosed _ hnear).2
  rw [hread] at h
  exact h

end PoincareConjecture.M47
