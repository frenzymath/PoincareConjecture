import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Blowup.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Extension.Canonical
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Extension.TerminalPinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.TerminalEstimates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Controlled.BoundsTheory









set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.DeepHorn

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



theorem terminalBlowupSequence_boundedDistance_hypotheses
    (hM04 : RicciFlowCurvatureCalculus.{u}) {epsilon C : ℝ}
    (hepsilon : ∀ k, (H k).epsilon = epsilon) (hC : ∀ k, (H k).constant = C)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 ≤
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k) :
    DenseGeneralizedBoundedDistanceHypotheses
      (terminalBlowupSequence H Q x hpos hdiv) epsilon C := by
  constructor
  · intro k
    have hp := extension_hamiltonIveyPinched hM04 (H k) (Q k).extension
    exact Or.inl ⟨fun t ht => (hp t ht).2.1, hp⟩
  · intro k
    simpa only [terminalBlowupSequence, hepsilon k, hC k] using
      (Q k).extension.earlier_dense_canonical_of_singularTimeAssumptions
        (H k) le_rfl (x k) (hcutoff k)



theorem terminalBlowupSequence_boundedDistance_and_compact
    (hM04 : RicciFlowCurvatureCalculus.{u}) (hM29 : DenseGeneralizedBoundedDistanceTheory.{u})
    {epsilon C : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_small : epsilon ≤ Classical.choose hM29.constants) (hC_pos : 0 < C)
    (hepsilon : ∀ k, (H k).epsilon = epsilon) (hC : ∀ k, (H k).constant = C)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 ≤
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k) :
    GeneralizedBlowupBoundedDistance (terminalBlowupSequence H Q x hpos hdiv) ∧
      BlowupBaseBallsCompact (terminalBlowupSequence H Q x hpos hdiv) := by
  have hb := (Classical.choose_spec hM29.constants).2.2 epsilon
    hepsilon_pos hepsilon_small C hC_pos (terminalBlowupSequence H Q x hpos hdiv)
    (terminalBlowupSequence_boundedDistance_hypotheses H Q x hpos hdiv
      hM04 hepsilon hC hcutoff)
  exact ⟨hb, terminalBlowupSequence_balls_compact H Q x hpos hdiv hb⟩



theorem terminalBlowupSequence_scalar_gradient_bound
    (hM04 : RicciFlowCurvatureCalculus.{u}) {B : ℝ}
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
    (hM04 : RicciFlowCurvatureCalculus.{u}) {B : ℝ}
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

end PoincareConjecture.DeepHorn
