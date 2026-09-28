import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_IntrinsicComparison
import PoincareConjecture.Definitions.M44CapPersistence
import PoincareConjecture.Proofs.M35.TerminalBlowup.MetricContraction










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46






theorem capComparison_metric_later_le_three_earlier
    {g0 : StandardInitialMetric} (P : RepairedCapPersistenceData.{u} g0)
    {F : SurgeryFlowData.{u}} (hinitial : F.standard_initial = g0)
    {S : MaximalStandardCapFlow F.standard_initial} (hS : HEq S P.standard_cap.flow)
    {t : ℝ} {A eta : ℝ} {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (chart : StandardCapSpace → (F.slice t).carrier)
    (comparison : SurgeryCapFamilyComparison F S A eta e chart)
    (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ J) (hs₂ : s₂ ∈ J) (horder : s₁ ≤ s₂)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A)
    (v : StandardCapSpace) :
    capComparisonCoefficients e chart s₂ hs₂ x v v ≤
      3 * capComparisonCoefficients e chart s₁ hs₁ x v v := by
  have htime₁ := comparison.choose_spec.2.2.1 s₁ hs₁
  have htime₂ := comparison.choose_spec.2.2.1 s₂ hs₂
  have hmodel : (S.metric s₂).inner x v v ≤ (S.metric s₁).inner x v v := by
    cases hinitial
    cases hS
    exact P.standard_cap.metric_inner_antitone x v htime₁ htime₂ horder
  have hnonneg : 0 ≤ (S.metric s₁).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((S.metric s₁).pos x v hv).le
  have hbefore := (capComparison_metric_bounds e chart comparison heta s₁ hs₁ hx v).1
  have hafter := (capComparison_metric_bounds e chart comparison heta s₂ hs₂ hx v).2
  have hfactor : (1 + eta) * (S.metric s₁).inner x v v ≤
      3 * ((1 - eta) * (S.metric s₁).inner x v v) := by
    have hh := mul_nonneg (sub_nonneg.mpr hetaHalf) hnonneg
    nlinarith
  calc
    _ ≤ (1 + eta) * (S.metric s₂).inner x v v := hafter
    _ ≤ (1 + eta) * (S.metric s₁).inner x v v :=
      mul_le_mul_of_nonneg_left hmodel (by linarith)
    _ ≤ 3 * ((1 - eta) * (S.metric s₁).inner x v v) := hfactor
    _ ≤ _ := mul_le_mul_of_nonneg_left hbefore (by norm_num)

end PoincareConjecture.Proofs.M46
