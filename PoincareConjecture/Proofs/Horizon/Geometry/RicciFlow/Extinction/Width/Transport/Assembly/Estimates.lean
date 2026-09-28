import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.LowerLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.Forward

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}

theorem m67_width_nonnegative
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (hwidth : M61WidthTheory.{u} q) (s : Set.Icc (0 : ℝ) T) : 0 ≤ X.width s := by
  rw [X.width_eq_based]
  exact (hwidth.based_class (X.slice s).metric (P.component s).compact
    (P.component s).connected (P.component s).basepoint
    (X.slice s).pi_two_trivial (X.slice s).alpha).nonnegative

theorem m67_conclusion_of_event_factor_bounds
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (hwidth : M61WidthTheory.{u} q)
    (hevent : ∀ s : Set.Icc (0 : ℝ) T,
      s.1 ∈ (↑P.surgery_times : Set ℝ) →
      ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
        ∀ t : Set.Icc (0 : ℝ) T, s.1 - delta < t.1 → t.1 < s.1 →
          X.width s ≤ (1 + eta) ^ 2 * X.width t) : M67Conclusion X where
  width_nonnegative := m67_width_nonnegative X hwidth
  forward_difference := m67_width_forward_difference X
  continuous_at_regular := m67_width_continuous_at_regular X
  surgery_lower_limit := fun s hs => m67_lower_limit_of_factor_bounds X.width s
    (m67_width_nonnegative X hwidth s) (hevent s hs)
  right_continuous_after_event := fun s _hs => m67_width_right_continuous X s

end PoincareConjecture
