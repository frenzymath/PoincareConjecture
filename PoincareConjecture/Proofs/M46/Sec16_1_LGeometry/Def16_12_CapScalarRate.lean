import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_IntrinsicScalar
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_PhysicalScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

theorem exists_actualCap_scalarRate_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {c theta A : ℝ}
    (hc : 0 < c) (htheta : theta < 1) (hA : 0 < A)
    (hrate : ∀ s ∈ Ico 0 P.standard_cap.flow.base.lifetime, ∀ x : StandardCapSpace,
      c / (1 - s) ≤ (P.standard_cap.flow.connection s).scalarCurvature x) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 / 2 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S P.standard_cap.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A),
      SurgeryCapFamilyComparison F S A eta e initial.chart →
      0 < F.parameters.h t → ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (e.forward s hs (initial.chart x)) := by
  let K : Set StandardCapSpace := {x | g0.metric.edist 0 x ≤ ENNReal.ofReal A}
  obtain ⟨eta, heta, hetaHalf, hbound⟩ :=
    exists_standardCap_intrinsic_scalarRate_tolerance P hc htheta hrate
      (M36.standard_closed_ball_compact g0 hA.le)
  refine ⟨eta, heta, hetaHalf, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial comparison hh s hs hst x hx
  have htime : s ∈ Icc 0 theta := ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  have hKx : x ∈ K := by
    dsimp only [K]
    rw [← hinitial]
    change F.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal A
    change F.standard_initial.metric.edist 0 x < ENNReal.ofReal A at hx
    exact le_of_lt hx
  have hjet : 2 ≤ ⌊eta⁻¹⌋₊ := by
    apply Nat.le_floor
    have := (le_div_iff₀ heta).mpr (show (2 : ℝ) * eta ≤ 1 by linarith)
    simpa only [one_div, Nat.cast_ofNat] using this
  have hU : IsOpen (F.standard_initial.metric.ball 0 A) :=
    (capInitialPartialDiffeomorph initial).open_source
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  have hUopen : IsOpen U := himage ▸ (capInitialPartialDiffeomorph initial).open_target
  have hmap : MapsTo initial.chart (F.standard_initial.metric.ball 0 A) U := by
    intro y hy
    exact himage ▸ mem_image_of_mem initial.chart hy
  have hsmooth := capComparisonCoefficients_smooth e hUopen hU initial.chart_smooth hmap s hs
  have hscalar : c / (2 * (1 - s)) ≤ M44.jetScalarCurvature
      (SpacetimeBounds.metricTwoJet (capComparisonCoefficients e initial.chart s hs) x) := by
    have hhbound := hbound s htime (F.standard_initial.metric.ball 0 A) hU
      (capComparisonCoefficients e initial.chart s hs) hsmooth x hKx hx
    apply hhbound
    intro j hj
    have he := (capComparison_covariant_error_lt e initial.chart comparison heta s hs hx
      (hj.trans hjet)).le
    cases hinitial
    cases hS
    exact he
  rw [capComparison_scalar_readout e initial comparison hh s hs hx] at hscalar
  have hsq : 0 < (F.parameters.h t) ^ 2 := sq_pos_of_pos hh
  rw [div_mul_eq_div_div]
  exact (div_le_iff₀ hsq).mpr (by simpa only [mul_comm] using hscalar)

end PoincareConjecture.Proofs.M46
