import PoincareConjecture.Statements.M50FinitePrefix








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




theorem m50SelectedLoss_from_M49
    (V49 : RepairedVolumeLossTheory.{u}) (V50 : RepairedFinitePrefixTheory.{u})
    (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants) :
    ∃ deltaUpper : ℝ, 0 < deltaUpper ∧ deltaUpper ≤ K.delta₀ ∧
      ∀ (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F),
        F.standard_initial = g₀ → F.local_constants = K →
        (∀ T ∈ F.surgery_times, F.parameters.delta T ≤ deltaUpper) →
        ∃ V : RepairedVolumeLossData F C,
          Nonempty (RepairedFinitePrefixData F C V) := by
  obtain ⟨deltaUpper, hpos, hle, losses, _count⟩ := V49.calibrated g₀ K
  refine ⟨deltaUpper, hpos, hle, ?_⟩
  intro F C hg₀ hK hdelta
  obtain ⟨V⟩ := losses F C hg₀ hK hdelta
  exact ⟨V, V50.finite_prefix F C V⟩

end PoincareConjecture
