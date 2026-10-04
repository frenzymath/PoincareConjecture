import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Terminal.TerminalLocalGeometry
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.NormalCoverService
import PoincareLib.Topology.Sequences.Diagonal

/-!
# All-radius normal covers of the actual terminal components

Morgan--Tian Theorem 5.9 and Corollary 5.10, pp. 88--89, and Claim 11.5,
p. 270. Fixed stage geometry feeds the precise local normal-cover service.
One strict selection retains every earlier stage and its actual curvature
derivative bounds. The normal-cover metric family is constant; no
stationary Ricci flow or common backward lifetime is asserted.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

/-- The actual normalized source components admit simultaneous finite
normal covers at all integer radii, with the derivative input for their
coordinate jets (Theorem 5.9 and Claim 11.5, pp. 88--89 and 270). -/
theorem exists_terminalComponent_normal_covers
    (hNormal : UniformNormalCoverService.{u})
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ R rho : ℕ → ℝ, ∃ N : ℕ → ℕ,
        (∀ j, 0 < rho j ∧ 2 * rho j < R j ∧ R j < 1) ∧
        (∀ k j, j ≤ k → Nonempty
          (NormalChartCover (fun _ => terminalComponentMetric S (sigma k))
            (terminalComponentBase S (sigma k)) (-1) 1
            ((j : ℝ) + 1) (R j) (rho j) (1 / 4) (9 / 4) (N j))) ∧
        ∀ j m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ k in atTop,
          ∀ x ∈ (terminalComponentMetric S (sigma k)).ball
              (terminalComponentBase S (sigma k)) ((j : ℝ) + 1 + R j),
            (terminalComponentMetric S (sigma k)).leviCivitaData.curvatureDerivativeNorm
              m x ≤ D := by
  obtain ⟨K, vlower, Vupper, hK, hv, hV, hgeometry⟩ :=
    exists_terminalComponent_local_geometry hC H hbound
  choose R rho N hrho hrhoR hR hfactory using fun j =>
    hNormal 3 (K := K j) (δ := 1) (v := vlower j) (V := Vupper j)
      (by norm_num) (hK j) zero_lt_one (hv j) (hV j)
  have hcovers (j : ℕ) : ∀ᶠ k in atTop, Nonempty
      (NormalChartCover (fun _ => terminalComponentMetric S k)
        (terminalComponentBase S k) (-1) 1 ((j : ℝ) + 1)
        (R j) (rho j) (1 / 4) (9 / 4) (N j)) := by
    filter_upwards [hgeometry j] with k hk
    let : PreconnectedSpace (terminalComponentCarrier S k).carrier :=
      ⟨(terminalComponentCarrier S k).connected.isPreconnected⟩
    exact hfactory j (terminalComponentCarrier S k).carrier
      (terminalComponentMetric S k) (terminalComponentMetric S k).leviCivitaData
      (terminalComponentBase S k) ((j : ℝ) + 1) ((j : ℝ) + 3)
      (by positivity) (by linarith) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
  obtain ⟨sigma, hsigma, hcover⟩ := Poincare.exists_strictMono_forall_le_of_eventually hcovers
  refine ⟨sigma, hsigma, R, rho, N, fun j => ⟨hrho j, hrhoR j, hR j⟩, hcover, ?_⟩
  intro j m
  have hRpos : 0 < R j := (mul_pos zero_lt_two (hrho j)).trans (hrhoR j)
  obtain ⟨D, hD, htail⟩ := eventually_terminalComponent_curvatureDerivativeNorm_le
    hC H hbound ((j : ℝ) + 1 + R j) (by positivity) m
  exact ⟨D, hD.le, hsigma.tendsto_atTop.eventually htail⟩

end PoincareMT.M30
