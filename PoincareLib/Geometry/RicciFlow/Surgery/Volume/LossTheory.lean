import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossData

/-!
Adapted from Mapher `PoincareMT/Statements/M49VolumeLoss.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M49 repaired surgery volume-loss statement

Natural-language theorem: fix the actual standard model and local surgery
constants. There is one positive upper cutoff for delta such that every
controlled flow using these data and satisfying that cutoff has selected
terminal loss bounds. Retained-volume transport and the post-volume bound
use the actual regular-limit metric, whose volume is bounded by the scalar
left limit of total pre-surgery volume. Weighted volume is nonincreasing, with
volume growth bounded by `exp (6 * (b - a))` on included time intervals.
Cap/neck events have positive loss at
the corrected `h^3 / delta` scale. Deletion-only events may use the lower
bound zero, and vanishing events have empty post-volume without any imposed
value for their left-limit volume.

For the same calibrated cutoff, fix a finite initial-volume upper bound,
a positive horizon, and a positive lower surgery height. One integer then
bounds all surgery times in every observed partial flow with these data.
The flow is raw `SurgeryFlowData`, without equality to a selected M36 result.
The M49 controls explicitly provide the pre-surgery interval/domain
compatibilities and the discarded positive-volume component for a zero-cap
nonempty event; these facts are not silently inferred from admissibility.
Only pinching and actual event controls on the observed interval are needed;
no future canonical/noncollapsing properties are assumed. The proof counts
all sphere cuts using volume and then component deletions using topology.

Source: Morgan--Tian, Lemma 17.12, pp. 410--411 (with Theorem 15.9,
pp. 363--366).  The printed `delta⁻¹ h²` term is dimensionally incorrect and
is corrected to `h^3 / delta` by `reviews/errata/2026-09-10-surgery-extinction-audit.md`
and erratum record `MT-SURGERY-VOLUME-SCALING`. The lower height is supplied
from Definition 15.5's common selector and the positive radius/delta lower
bounds when this service is applied to an epoch. M49 uses the static model
and the actual local surgery results stored in each event; cap persistence
and continuation are not theorem-level premises of this volume argument.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedVolumeLossTheory : Prop where
  /-- One calibrated cutoff supplies both the selected event-loss service
      and the uniform raw-flow count. The count is chosen before the flow. -/
  calibrated : ∀ (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants),
    ∃ deltaUpper : ℝ, 0 < deltaUpper ∧ deltaUpper ≤ K.delta₀ ∧
      (∀ F : SurgeryFlowData.{u},
        ∀ C : RepairedVolumeLossControls F,
          F.standard_initial = g₀ → F.local_constants = K →
          (∀ T ∈ F.surgery_times, F.parameters.delta T ≤ deltaUpper) →
          Nonempty (RepairedVolumeLossData F C)) ∧
      (∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
        0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
        ∃ n : ℕ, ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          F.standard_initial = g₀ → F.local_constants = K → O.H ≤ B →
          RepairedObservedVolumeControls F O →
          calibratedMetricVolume (F.metric 0) Set.univ ≤ V₀ →
          (∀ T ∈ F.surgery_times ∩ surgeryObservationInterval O,
            F.parameters.delta T ≤ deltaUpper ∧ hMin ≤ F.parameters.h T) →
          ∀ S : Finset ℝ,
            (↑S : Set ℝ) ⊆ F.surgery_times ∩ surgeryObservationInterval O →
              S.card ≤ n)

end PoincareMT
