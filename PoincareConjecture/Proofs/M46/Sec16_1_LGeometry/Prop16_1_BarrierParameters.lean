import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_SafeConstants
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_BirthMetric
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_CapScalarRate
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_EpochWindow










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46



noncomputable def positiveActionBudget {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : ℝ :=
  actionBudget p + 4 * surgeryEpochStart (p.i + 1) *
    Real.sqrt (surgeryEpochStart (p.i + 1))

theorem positiveActionBudget_pos {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : 0 < positiveActionBudget p := by
  have hH : 0 < surgeryEpochStart (p.i + 1) :=
    (by norm_num : (0 : ℝ) < 1 / 32).trans_le (epochStart_ge_initial _)
  unfold positiveActionBudget actionBudget
  positivity




structure ActionBarrierParameters (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (rho : ℝ) where
  safeTime : ℝ
  safeTime_pos : 0 < safeTime
  safeTime_metric : safeTime ≤ rho ^ 2 / 12
  safeTime_interval : safeTime ≤ rho ^ 2 / 4
  safeTime_action : positiveActionBudget p < rho ^ 2 / (16 * Real.sqrt safeTime)
  c : ℝ
  c_pos : 0 < c
  theta : ℝ
  theta_half : 1 / 2 < theta
  theta_one : theta < 1
  top_barrier : positiveActionBudget p / Real.sqrt safeTime <
    -(c / 2) * (Real.log (1 - theta) + Real.log 2)
  mu : ℝ
  mu_pos : 0 < mu
  A : ℝ
  A_pos : 0 < A
  A_buffer : S.standard_initial.cylindrical_end.radius + 5 < A / 2
  side_barrier : positiveActionBudget p / Real.sqrt safeTime < mu * A ^ 2 / 4
  eta : ℝ
  eta_pos : 0 < eta
  eta_half : eta ≤ 1 / 2
  metric_bound : ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = S.standard_initial)
      (model : MaximalStandardCapFlow F.standard_initial),
    HEq model S.cap_persistence.standard_cap.flow →
    ∀ (t : ℝ) (J : Set ℝ) (U : Set (F.slice t).carrier)
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
      (chart : StandardCapSpace → (F.slice t).carrier),
    SurgeryCapFamilyComparison F model A eta e chart → ∀ hzero : (0 : ℝ) ∈ J,
    ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
    ∀ x ∈ F.standard_initial.metric.ball 0 A, ∀ v : StandardCapSpace,
      mu * capComparisonCoefficients e chart 0 hzero x v v ≤
        capComparisonCoefficients e chart s hs x v v
  scalar_bound : ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = S.standard_initial)
      (model : MaximalStandardCapFlow F.standard_initial),
    HEq model S.cap_persistence.standard_cap.flow →
    ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
      (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
      (initial : SurgeryCapInitialComparison F t hT i A),
    SurgeryCapFamilyComparison F model A eta e initial.chart →
    0 < F.parameters.h t → ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
    ∀ x ∈ F.standard_initial.metric.ball 0 A,
      c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward s hs (initial.chart x))




theorem exists_actionBarrierParameters (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) {rho : ℝ} (hrho : 0 < rho) :
    Nonempty (ActionBarrierParameters S p rho) := by
  obtain ⟨a, ha, hametric, hatime, haaction⟩ :=
    exists_initialSafeDuration hrho (positiveActionBudget_pos p).le
  obtain ⟨c, hc, hrate, htop⟩ := exists_standardCapTopBarrier S.cap_persistence
  obtain ⟨theta, hhalf, hone, hbarrier⟩ := htop (positiveActionBudget p / Real.sqrt a)
  have htheta : 0 ≤ theta := by linarith
  obtain ⟨mu, hmu, hmetric⟩ :=
    exists_actualCap_birth_metric_factor S.cap_persistence htheta hone
  obtain ⟨A, hA, hbuffer, hside⟩ := exists_metricCapSideRadius hmu
    (positiveActionBudget p / Real.sqrt a) (S.standard_initial.cylindrical_end.radius + 5)
  obtain ⟨eta, heta, hetaHalf, hscalar⟩ :=
    exists_actualCap_scalarRate_tolerance S.cap_persistence hc hone hA hrate
  refine ⟨{
    safeTime := a
    safeTime_pos := ha
    safeTime_metric := hametric
    safeTime_interval := hatime
    safeTime_action := haaction
    c := c
    c_pos := hc
    theta := theta
    theta_half := hhalf
    theta_one := hone
    top_barrier := hbarrier
    mu := mu
    mu_pos := hmu
    A := A
    A_pos := hA
    A_buffer := hbuffer
    side_barrier := hside
    eta := eta
    eta_pos := heta
    eta_half := hetaHalf
    metric_bound := ?_
    scalar_bound := hscalar
  }⟩
  intro F hinitial model hmodel t J U e chart hcomparison hzero s hs hst x hx v
  exact hmetric F hinitial model hmodel t A eta J U e chart hcomparison heta hetaHalf
    hzero s hs hst x hx v

end PoincareConjecture.Proofs.M46
