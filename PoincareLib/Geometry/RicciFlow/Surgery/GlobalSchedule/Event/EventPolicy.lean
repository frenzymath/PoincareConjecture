import PoincareLib.Geometry.RicciFlow.Surgery.Flow.TerminalPolicy
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory

/-!
# Vanishing policy under a fixed pre-carrier identification

MT Definition 15.8 and Section 17.2, pp. 362 and 409-411. A copied global
event retains its source event's strict scalar-margin witnesses. Its
pre-carrier may differ, so use the actual fixed metric identification and
the supplied M13 scalar identity, not equality of complete pre-flow data.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.SurgeryVanishingEventData

/-- A fixed isometry of the actual pre-flows transports the same witnesses
at every later time in their common preinterval. -/
theorem transportTerminalPolicy
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    {P₀ P₁ : SurgeryParameters} {slice₀ slice₁ : ℝ → GeneralizedSliceCarrier.{u}}
    {metric₀ : ∀ t, RiemannianMetric 3 (slice₀ t).carrier}
    {metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier} {T : ℝ}
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    (B : SurgeryVanishingEventData P₁ slice₁ metric₁ T)
    (parameters : P₁ = P₀) (reference : B.tMinus = A.tMinus)
    (e : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ B.tMinus).carrier (slice₀ A.tMinus).carrier ∞)
    (hmetric : ∀ t ∈ Set.Ico B.tMinus T,
      MetricHomothety (B.pre_flow.metric t) (A.pre_flow.metric t) e 1)
    (policy : SurgeryVanishingEventTerminalPolicy A) :
    SurgeryVanishingEventTerminalPolicy B := by
  intro x
  obtain ⟨L, hL, s, hs, hscalar⟩ := policy (e x)
  have hs' : s ∈ Set.Ico B.tMinus T := by simpa only [reference] using hs
  refine ⟨L, ?_, s, hs', ?_⟩
  · simpa only [parameters] using hL
  · intro t ht
    have htpre : t ∈ Set.Ico B.tMinus T := ⟨hs'.1.trans ht.1, ht.2⟩
    have geometry := m13.metric_homothety _ _
      (B.pre_flow.metric t) (A.pre_flow.metric t) e 1 (by norm_num) (hmetric t htpre)
    exact (hscalar t ht).trans_eq (by
      simpa only [div_one] using
        geometry.scalar_eq (B.pre_flow.connection t) (A.pre_flow.connection t) x)

end PoincareMT.SurgeryVanishingEventData
