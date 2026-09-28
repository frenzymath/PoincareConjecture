import PoincareConjecture.Proofs.M32.Claim11_32.Extension.AnalyticTime
import PoincareConjecture.Proofs.M32.Claim11_32.Sequence

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
  (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
  (Q : ∀ k, SingularLimitConclusion (H k))
  (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
  (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
  (hdiv : Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)

theorem terminalBlowupSequence_scalar_gradient_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) {B : ℝ}
    (hB : ∀ k, (H k).analytic_constant = B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k)
    (k : ℕ) (t : ℝ) (ht : t ∈ (Q k).extension.extended.interval)
    (y : ((Q k).extension.extended.slice t).carrier)
    (hy : 4 * (terminalBlowupSequence H Q x hpos hdiv).scale k ≤
      ((Q k).extension.extended.connection t).scalarCurvature y)
    (v : TangentSpace (𝓡 3) y)
    (hv : ((Q k).extension.extended.metric t).inner y v v = 1) :
    |mvfderiv (𝓡 3) ((Q k).extension.extended.connection t).scalarCurvature y v| ≤
      B * ((Q k).extension.extended.connection t).scalarCurvature y ^ (3 / 2 : ℝ) := by
  simpa only [hB k] using extension_scalar_gradient_bound_of_strict
    hM04 (H k) (Q k).extension t ht y ((hcutoff k).trans_le hy) v hv

theorem terminalBlowupSequence_scalar_time_derivative_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) {B : ℝ}
    (hB : ∀ k, (H k).analytic_constant = B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k)
    (k : ℕ) (b : (Q k).extension.extended.box_index) (t : ℝ)
    (ht : t ∈ ((Q k).extension.extended.box b).interval)
    (y : ((Q k).extension.extended.box b).carrier.carrier)
    (hy : 4 * (terminalBlowupSequence H Q x hpos hdiv).scale k ≤
      (((Q k).extension.extended.box b).flow.connection t).scalarCurvature y) :
    ∃ d : ℝ, HasDerivWithinAt
      (fun s => (((Q k).extension.extended.box b).flow.connection s).scalarCurvature y) d
      ((Q k).extension.extended.box b).interval t ∧
      |d| ≤ B * (((Q k).extension.extended.box b).flow.connection t).scalarCurvature y ^ 2 := by
  simpa only [hB k] using extension_scalar_time_derivative_bound
    hM04 (H k) (Q k).extension b t ht y ((hcutoff k).trans_le hy)

end PoincareConjecture.M32
