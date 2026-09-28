import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_IntrinsicComparison
import PoincareConjecture.Definitions.M44CapPersistence
import PoincareConjecture.Proofs.M04.MetricComparison










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46





theorem exists_standardCap_birth_metric_factor {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ s ∈ Icc 0 theta, ∀ x : StandardCapSpace,
      ∀ v : StandardCapSpace,
        (3 * mu) * (P.standard_cap.flow.metric 0).inner x v v ≤
          (P.standard_cap.flow.metric s).inner x v v := by
  have htheta : theta < P.standard_cap.flow.base.lifetime := by
    rwa [P.standard_cap.lifetime_one]
  obtain ⟨K, hK, hcurv⟩ :=
    P.standard_cap.flow.base.curvature_locally_bounded theta htheta0 htheta
  let mu := Real.exp (-6 * K * theta) / 3
  have hmu : 0 < mu := div_pos (Real.exp_pos _) (by norm_num)
  refine ⟨mu, hmu, ?_⟩
  intro s hs x v
  have htime0 : (0 : ℝ) ∈ Ico 0 P.standard_cap.flow.base.lifetime :=
    ⟨le_rfl, P.standard_cap.flow.base.lifetime_pos⟩
  have htimes : s ∈ Ico 0 P.standard_cap.flow.base.lifetime :=
    ⟨hs.1, hs.2.trans_lt htheta⟩
  have hcompare := (P.standard_cap.flow.base.flow.metric_comparison_of_curvature_bound
    htime0 htimes hs.1 hK
      (fun t ht y => (le_abs_self _).trans (hcurv t ⟨ht.1, ht.2.trans hs.2⟩ y)) x v).1
  have hnonneg : 0 ≤ (P.standard_cap.flow.metric 0).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((P.standard_cap.flow.metric 0).pos x v hv).le
  have hexp : Real.exp (-6 * K * theta) ≤ Real.exp (-6 * K * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hs.2)]
  calc
    _ = Real.exp (-6 * K * theta) *
        (P.standard_cap.flow.metric 0).inner x v v := by dsimp only [mu]; ring
    _ ≤ Real.exp (-6 * K * s) * (P.standard_cap.flow.metric 0).inner x v v :=
      mul_le_mul_of_nonneg_right hexp hnonneg
    _ ≤ _ := by
      simpa only [MaximalStandardCapFlow.metric, Nat.cast_ofNat, sub_zero, neg_mul,
        show (2 : ℝ) * 3 = 6 by norm_num]
        using hcompare





theorem exists_actualCap_birth_metric_factor {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) :
    ∃ mu : ℝ, 0 < mu ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S P.standard_cap.flow →
      ∀ (t A eta : ℝ) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (chart : StandardCapSpace → (F.slice t).carrier),
      SurgeryCapFamilyComparison F S A eta e chart →
      0 < eta → eta ≤ 1 / 2 → ∀ hzero : (0 : ℝ) ∈ J,
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A, ∀ v : StandardCapSpace,
        mu * capComparisonCoefficients e chart 0 hzero x v v ≤
          capComparisonCoefficients e chart s hs x v v := by
  obtain ⟨mu, hmu, hmodel⟩ := exists_standardCap_birth_metric_factor P htheta0 htheta1
  refine ⟨mu, hmu, ?_⟩
  intro F hinitial S hS t A eta J U e chart comparison heta hetaHalf hzero s hs hst x hx v
  have hmodel' : (3 * mu) * (S.metric 0).inner x v v ≤ (S.metric s).inner x v v := by
    have hs0 := (comparison.choose_spec.2.2.1 s hs).1
    cases hinitial
    cases hS
    exact hmodel s ⟨hs0, hst⟩ x v
  have hnonneg : 0 ≤ (S.metric 0).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((S.metric 0).pos x v hv).le
  have hbefore := (capComparison_metric_bounds e chart comparison heta 0 hzero hx v).2
  have hafter := (capComparison_metric_bounds e chart comparison heta s hs hx v).1
  have hfactor : mu * ((1 + eta) * (S.metric 0).inner x v v) ≤
      (1 - eta) * ((3 * mu) * (S.metric 0).inner x v v) := by
    have hh := mul_nonneg (mul_nonneg hmu.le (sub_nonneg.mpr hetaHalf)) hnonneg
    nlinarith
  calc
    _ ≤ mu * ((1 + eta) * (S.metric 0).inner x v v) :=
      mul_le_mul_of_nonneg_left hbefore hmu.le
    _ ≤ (1 - eta) * ((3 * mu) * (S.metric 0).inner x v v) := hfactor
    _ ≤ (1 - eta) * (S.metric s).inner x v v :=
      mul_le_mul_of_nonneg_left hmodel' (by linarith)
    _ ≤ _ := hafter

end PoincareConjecture.Proofs.M46
