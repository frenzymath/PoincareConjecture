import PoincareConjecture.Proofs.M03.Existence.IntegralGaugeRecovery
import PoincareConjecture.Proofs.M03.Existence.MetricPerturbationNative

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.IntegralGaugeRecovery

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

local notation "Fiber" =>
  fun x : M => TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ

noncomputable def certificate_of_metric_path
    {g₀ : RiemannianMetric n M} {T : ℝ}
    (P : SmallMetricPath g₀ (Set.Ico (0 : ℝ) T)) (hT : 0 < T)
    (D : ∀ t : ℝ, LeviCivitaData (P.metric t))
    (source gauge : ∀ (_t : ℝ) (x : M), Fiber x)
    (hsource : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      ContinuousOn (fun s => source s x u v) (Set.Ico (0 : ℝ) T))
    (hgauge : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      ContinuousOn (fun s => gauge s x u v) (Set.Ico (0 : ℝ) T))
    (hint : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (x : M)
      (u v : TangentSpace (𝓡 n) x),
      (P.metric t).inner x u v = g₀.inner x u v +
        ∫ s in (0 : ℝ)..t, (source s x u v - gauge s x u v))
    (hcancel : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) T →
      ∀ (D' : LeviCivitaData (P.metric t)) (x : M)
        (u v : TangentSpace (𝓡 n) x),
      source t x u v - gauge t x u v = -2 * D'.ricci x u v) :
    Certificate (n := n) (M := M) g₀ := by
  refine
    { T := T
      hT := hT
      metric := P.metric
      connection := D
      smooth := P.metric_isSmoothFamilyOn
      initial := P.metric_initial
      source := source
      gaugeCorrection := gauge
      source_continuous := ?_
      integral_equation := hint
      cancellation := hcancel }
  intro x u v
  exact (hsource x u v).sub (hgauge x u v)

end PoincareConjecture.IntegralGaugeRecovery

end
