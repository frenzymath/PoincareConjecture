import PoincareConjecture.Proofs.M47.CanonicalStandardTimeJets
import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 SpacetimeBounds Proofs.M46

noncomputable local instance capNearbyCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capNearbyCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace



theorem exists_actualCap_nearby_coordinate_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A nu : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (m : ℕ) (hnu : 0 < nu) :
    ∃ eta0 delta : ℝ, 0 < eta0 ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ v ∈ Icc 0 theta, |s - v| < delta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (capComparisonCoefficients e initial.chart s hs) x -
          iteratedFDeriv ℝ j (S.metric v).euclideanCoefficients x‖ ≤ nu := by
  obtain ⟨C, hC, hcoordinate⟩ :=
    exists_actualCap_coordinate_derivative_bound standard htheta hA m
  obtain ⟨delta, hdelta, htime⟩ := standard_metric_jets_uniform_time_delta standard.flow
    (by simpa only [standard.lifetime_one] using htheta)
    (M36.standard_closed_ball_compact g0 hA.le) m (half_pos hnu)
  refine ⟨min (1 / ((m : ℝ) + 1)) (nu / (2 * C)), delta,
    lt_min (by positivity) (div_pos hnu (mul_pos (by norm_num) hC)), hdelta, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta heta0 comparison s hs hst
    v hv hnear x hx j hj
  have hfirst := hcoordinate F hinitial S hS t hT hn i J U e initial eta heta
    (heta0.trans (min_le_left _ _)) comparison s hs hst x hx j hj
  have hproduct : C * eta ≤ nu / 2 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).mp
      (heta0.trans (min_le_right _ _))
    nlinarith
  have hstime : s ∈ Icc 0 theta := ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  have hclosed : x ∈ {y | g0.metric.edist 0 y ≤ ENNReal.ofReal A} := by
    rw [← hinitial]
    exact (show F.standard_initial.metric.edist 0 x < ENNReal.ofReal A from hx).le
  cases hinitial
  cases hS
  have hsecond := htime s hstime v hv hnear x hclosed j hj
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (capComparisonCoefficients e initial.chart s hs) x -
          iteratedFDeriv ℝ j (standard.flow.metric s).euclideanCoefficients x‖ +
        ‖iteratedFDeriv ℝ j (standard.flow.metric s).euclideanCoefficients x -
          iteratedFDeriv ℝ j (standard.flow.metric v).euclideanCoefficients x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ nu / 2 + nu / 2 := add_le_add (hfirst.trans hproduct) hsecond.le
    _ = nu := by ring



theorem exists_actualCap_nearby_analytic_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A nu : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hnu : 0 < nu) :
    ∃ eta0 delta : ℝ, 0 < eta0 ∧ 0 < delta ∧
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
      ∀ v ∈ Icc 0 theta, |s - v| < delta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
      let h := F.parameters.h t
      let D := F.connection (t + s / (h⁻¹ ^ 2))
      let p := e.forward s hs (initial.chart x)
      ‖(h ^ 2 * D.scalarCurvature p,
          h ^ 3 * scalarGradientNorm (F.metric (t + s / (h⁻¹ ^ 2))) D p,
          h ^ 4 * (D.laplacian D.scalarCurvature p + 2 * D.ricciNormSq p)) -
        ((S.connection v).scalarCurvature x,
          scalarGradientNorm (S.metric v) (S.connection v) x,
          (S.connection v).laplacian (S.connection v).scalarCurvature x +
            2 * (S.connection v).ricciNormSq x)‖ ≤ nu := by
  obtain ⟨eta0, heta0, hanalytic⟩ :=
    exists_actualCap_analytic_comparison_tolerance standard htheta hA (half_pos hnu)
  obtain ⟨delta, hdelta, htime⟩ := standard_analytic_uniform_time_delta standard.flow
    (by simpa only [standard.lifetime_one] using htheta)
    (M36.standard_closed_ball_compact g0 hA.le) (half_pos hnu)
  refine ⟨eta0, delta, heta0, hdelta, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetamax comparison hh s hs hst
    v hv hnear x hx
  have hfirst := hanalytic F hinitial S hS t hT hn i J U e initial eta heta hetamax
    comparison hh s hs hst x hx
  have hstime : s ∈ Icc 0 theta := ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  have hclosed : x ∈ {y | g0.metric.edist 0 y ≤ ENNReal.ofReal A} := by
    rw [← hinitial]
    exact (show F.standard_initial.metric.edist 0 x < ENNReal.ofReal A from hx).le
  cases hinitial
  cases hS
  have hsecond := htime s hstime v hv hnear x hclosed
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hfirst hsecond.le).trans (by linarith))

end PoincareConjecture.Proofs.M47
