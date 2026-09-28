import PoincareConjecture.Proofs.M47.TerminalCommonIntervalFloorScale

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCommonInterval_after_finite_germ_floor
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (V : GeneralizedBlowupSequence.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hfinite : ∃ K : ℝ, 1 ≤ K ∧ ∀ x : M, D.curvatureTensorNorm x ≤ K)
    {eta : ℝ} (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hthreshold : ∀ k, (r k)⁻¹ ^ 2 ≤ V.scale k) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∃ Delta : ℝ, Delta = terminalCommonIntervalDuration S B K ∧
        0 < Delta ∧ Delta ≤ 1 ∧
        ∀ᶠ k in atTop,
          64 * (2 * Delta + 1) ≤ V.scale k ∧
          B.curvature_threshold ≤ V.scale k ∧
          blowupPinchingThreshold (8 * K) eta ≤ V.scale k ∧
          (r k)⁻¹ ^ 2 ≤ V.scale k ∧
          0 < V.scale k ∧
          0 < (V.scale k * (r k) ^ 2)⁻¹ ∧
          (V.scale k * (r k) ^ 2)⁻¹ ≤ 1 ∧
          (r k)⁻¹ ^ 2 / V.scale k = (V.scale k * (r k) ^ 2)⁻¹ ∧
          (V.scale k)⁻¹ = (V.scale k * (r k) ^ 2)⁻¹ * (r k) ^ 2 := by
  obtain ⟨K, hK, _hbound⟩ := hfinite
  obtain ⟨Delta, hDelta, hDeltaPos, hDeltaLe, hEventually⟩ :=
    terminalCommonInterval_after_terminal_curvature_floor S B V hK r hr hthreshold
  exact ⟨K, hK, Delta, hDelta, hDeltaPos, hDeltaLe, hEventually⟩

end PoincareConjecture.M47
