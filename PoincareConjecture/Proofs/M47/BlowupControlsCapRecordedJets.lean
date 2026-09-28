import PoincareConjecture.Proofs.M47.BlowupControlsCapDerivativeJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

noncomputable local instance capRecordedCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capRecordedCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace



theorem exists_actualCap_coordinate_derivative_bound {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ 1 / ((m : ℝ) + 1) →
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (capComparisonCoefficients e initial.chart s hs) x -
          iteratedFDeriv ℝ j (S.metric s).euclideanCoefficients x‖ ≤ C * eta := by
  obtain ⟨C, hC, hbound⟩ := exists_standardCap_intrinsic_derivative_bound standard.flow
    (by simpa only [standard.lifetime_one] using htheta)
    (M36.standard_closed_ball_compact g0 hA.le) m
  refine ⟨C, hC, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaOrder comparison s hs hst x hx j hj
  have htime : s ∈ Icc 0 theta := ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  have hjet : m ≤ ⌊eta⁻¹⌋₊ := by
    apply Nat.le_floor
    have hproduct := (le_div_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mp hetaOrder
    have h := (le_div_iff₀ heta).mpr (show (m : ℝ) * eta ≤ 1 by nlinarith)
    simpa only [one_div] using h
  have hV : IsOpen (F.standard_initial.metric.ball 0 A) :=
    (capInitialPartialDiffeomorph initial).open_source
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := himage ▸ (capInitialPartialDiffeomorph initial).open_target
  have hmap : MapsTo initial.chart (F.standard_initial.metric.ball 0 A) U := by
    intro y hy
    exact himage ▸ mem_image_of_mem initial.chart hy
  have hsmooth := capComparisonCoefficients_smooth e hU hV initial.chart_smooth hmap s hs
  have hclosed : x ∈ {y | g0.metric.edist 0 y ≤ ENNReal.ofReal A} := by
    rw [← hinitial]
    change F.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal A
    change F.standard_initial.metric.edist 0 x < ENNReal.ofReal A at hx
    exact hx.le
  have hnorm (k : ℕ) (hk : k ≤ m) :=
    (capComparison_covariant_error_lt e initial.chart comparison heta s hs hx
      (hk.trans hjet)).le
  cases hinitial
  cases hS
  exact hbound s htime _ hV _ hsmooth x hclosed hx eta heta.le hnorm j hj

end PoincareConjecture.M47
