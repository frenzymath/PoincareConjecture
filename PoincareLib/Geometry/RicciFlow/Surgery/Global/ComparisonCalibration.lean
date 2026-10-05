import PoincareLib.Geometry.RicciFlow.Surgery.Global.SelectedCertificate
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A control chosen before the global flow

Definition 15.7 permits any positive non-increasing control below the schedule.
Halving a later schedule entry and imposing an absolute cutoff gives the strict
comparison bounds of Proposition 15.12 on the flow constructed with that control.
Sources: Morgan--Tian pp. 360, 363--365; the bounded contract is in
`reviews/contracts/2026-09-17-comparison-calibration-round1.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Positive antitone control fixed from the schedule before choosing a flow. -/
noncomputable def m52ComparisonControl {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (t : ℝ) : ℝ :=
  min (S.Delta ⌈32 * t⌉₊ / 2) (min 1 (K.R₀ ^ (-1 / 2 : ℝ) / 2))

theorem m52ComparisonControl_pos {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (t : ℝ) : 0 < m52ComparisonControl S t := by
  exact lt_min (div_pos (S.Delta_pos _) (by norm_num))
    (lt_min zero_lt_one
      (div_pos (Real.rpow_pos_of_pos K.R₀_pos _) (by norm_num)))

theorem m52ComparisonControl_antitone {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) : Antitone (m52ComparisonControl S) := by
  intro a b hab
  exact min_le_min
    (div_le_div_of_nonneg_right
      (S.Delta_antitone (Nat.ceil_mono (by linarith))) (by norm_num)) le_rfl

/-- The ceiling index runs at least as far as the dyadic epoch index. -/
theorem m52ComparisonControl_le_epoch {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (j : ℕ) {t : ℝ}
    (ht : t ∈ surgeryEpochEntry j) : m52ComparisonControl S t ≤ S.Delta j := by
  have hindex : j ≤ ⌈32 * t⌉₊ := by
    cases j with
    | zero => exact Nat.zero_le _
    | succ n =>
        have htime : (2 : ℝ) ^ n / 32 ≤ t := by
          simpa [surgeryEpochEntry, surgeryEpochStart] using ht.1
        have hpower : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
          exact_mod_cast Nat.succ_le_of_lt (show n < 2 ^ n from Nat.lt_two_pow_self)
        have hceil := Nat.le_ceil (32 * t)
        have hcast : ((n + 1 : ℕ) : ℝ) ≤ (⌈32 * t⌉₊ : ℝ) := by
          push_cast
          linarith
        exact_mod_cast hcast
  exact (min_le_left _ _).trans
    ((div_le_self (S.Delta_pos _).le (by norm_num)).trans (S.Delta_antitone hindex))

/-- The literal Definition 15.7 initial cutoff is strict, not just the larger
Theorem 13.2 cutoff stored in the metric-surgery constants. -/
theorem m52ComparisonControl_lt_initial {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (t : ℝ) : m52ComparisonControl S t < S.Delta 0 := by
  have hhalf : m52ComparisonControl S t ≤ S.Delta 0 / 2 :=
    (min_le_left _ _).trans (div_le_div_of_nonneg_right
      (S.Delta_antitone (Nat.zero_le _)) (by norm_num))
  linarith [S.Delta_pos 0]

theorem m52ComparisonControl_bounds {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (t : ℝ) :
    m52ComparisonControl S t ≤ K.delta₀ / 2 ∧
      m52ComparisonControl S t ≤ 1 ∧
      m52ComparisonControl S t ≤ K.R₀ ^ (-1 / 2 : ℝ) / 2 := by
  exact ⟨(min_le_left _ _).trans
      (div_le_div_of_nonneg_right (S.Delta_le _) (by norm_num)),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

/-- For the exact global flow constructed with this control, every nonnegative
time has strict delta and height bounds, with explicit half-bound margins.
This transports existing output identities; it does not change a flow. -/
theorem m52StrictComparisonBounds
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K)
    (hK : G.schedule.flow.local_constants = K)
    (hdelta : G.schedule.control_function = m52ComparisonControl S)
    (t : ℝ) (ht : 0 ≤ t) :
    G.certificate.flow.parameters.delta t < S.Delta 0 ∧
    G.certificate.flow.parameters.delta t ≤ G.certificate.flow.local_constants.delta₀ / 2 ∧
    G.certificate.flow.parameters.h t ≤
      G.certificate.flow.local_constants.R₀ ^ (-1 / 2 : ℝ) / 2 ∧
    G.certificate.flow.parameters.delta t < G.certificate.flow.local_constants.delta₀ ∧
    G.certificate.flow.parameters.h t <
      G.certificate.flow.local_constants.R₀ ^ (-1 / 2 : ℝ) := by
  rw [G.flow_eq]
  have hmem : t ∈ G.schedule.flow.time_domain := by
    rw [G.schedule.time_domain_eq]
    exact ht
  have heq : G.schedule.flow.parameters.delta t = m52ComparisonControl S t :=
    (G.schedule.control_eq t hmem).trans (congrFun hdelta t)
  obtain ⟨hd, hd1, hdH⟩ := m52ComparisonControl_bounds S t
  rw [← heq] at hd hd1 hdH
  have hd0 := (G.schedule.flow.parameters.delta_pos t ht).le
  have hr1 : G.schedule.flow.parameters.r t ≤ 1 :=
    (G.schedule.flow.parameters.r_le_epsilon t ht).trans
      (G.schedule.flow.parameters.epsilon_le.trans (by norm_num))
  have hh : G.schedule.flow.parameters.h t ≤ G.schedule.flow.parameters.delta t := by
    calc
      _ ≤ G.schedule.flow.parameters.delta t ^ 2 * G.schedule.flow.parameters.r t :=
        G.schedule.flow.parameters.h_le t ht
      _ ≤ G.schedule.flow.parameters.delta t ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hr1 (sq_nonneg _)
      _ ≤ G.schedule.flow.parameters.delta t := by nlinarith
  have hheight := hh.trans hdH
  rw [hK]
  exact ⟨by rw [heq]; exact m52ComparisonControl_lt_initial S t,
    hd, hheight, by linarith [K.delta₀_pos],
    by linarith [Real.rpow_pos_of_pos K.R₀_pos (-1 / 2 : ℝ)]⟩

end PoincareMT
