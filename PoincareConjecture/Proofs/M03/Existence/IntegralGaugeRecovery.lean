import PoincareConjecture.Proofs.M03.Existence.GaugeRecovery
import PoincareConjecture.Proofs.M03.Existence.DeTurckGaugeSign











set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

namespace IntegralGaugeRecovery

structure Certificate (g₀ : RiemannianMetric n M) where
  T : ℝ
  hT : 0 < T
  metric : ℝ → RiemannianMetric n M
  connection : ∀ t : ℝ, LeviCivitaData (metric t)
  smooth : RiemannianMetric.IsSmoothFamilyOn metric (Set.Ico 0 T)
  initial : metric 0 = g₀
  source : ∀ (t : ℝ) (x : M),
    TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ
  gaugeCorrection : ∀ (t : ℝ) (x : M),
    TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ
  source_continuous : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
    ContinuousOn (fun s => source s x u v - gaugeCorrection s x u v)
      (Set.Ico 0 T)
  integral_equation : ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (x : M)
    (u v : TangentSpace (𝓡 n) x),
    (metric t).inner x u v = g₀.inner x u v +
      ∫ s in (0 : ℝ)..t, source s x u v - gaugeCorrection s x u v
  cancellation : ∀ (t : ℝ), t ∈ Set.Ico 0 T →
    ∀ (D : LeviCivitaData (metric t)) (x : M)
      (u v : TangentSpace (𝓡 n) x),
      source t x u v - gaugeCorrection t x u v = -2 * D.ricci x u v

theorem derivative
    {g₀ : RiemannianMetric n M} (C : Certificate (n := n) (M := M) g₀)
    (t : ℝ) (ht : t ∈ Set.Ico 0 C.T) (D : LeviCivitaData (C.metric t))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (C.metric s).inner x u v)
      (-2 * D.ricci x u v) (Set.Ico 0 C.T) t := by
  have hsrc : ContinuousOn
      (fun s => C.source s x u v - C.gaugeCorrection s x u v)
      (Set.Ico 0 C.T) := C.source_continuous x u v
  have hderiv := DeTurckNative.hasDerivWithinAt_metric_of_intervalIntegral_Ico
    (g₀ := g₀) (g := C.metric)
    (h := fun s p a b => C.source s p a b - C.gaugeCorrection s p a b)
    (hcont := fun p a b => C.source_continuous p a b)
    (hint := C.integral_equation) ht x u v
  exact hderiv.congr_deriv (C.cancellation t ht D x u v)

theorem exists_metricFamily
    {g₀ : RiemannianMetric n M} (C : Certificate (n := n) (M := M) g₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g₀ ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (D : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D.ricci x u v) (Set.Ico 0 T) t := by
  refine ⟨C.T, C.hT, C.metric, C.initial, C.smooth, ?_⟩
  intro t ht D x u v
  exact derivative C t ht D x u v

end IntegralGaugeRecovery

end PoincareConjecture
