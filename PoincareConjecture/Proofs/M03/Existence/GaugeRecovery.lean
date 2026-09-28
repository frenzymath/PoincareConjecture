import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

namespace GaugeRecovery

structure Certificate (g0 : RiemannianMetric n M) where
  T : ℝ
  hT : 0 < T
  metric : ℝ → RiemannianMetric n M
  connection : ∀ t : ℝ, LeviCivitaData (metric t)
  smooth : RiemannianMetric.IsSmoothFamilyOn metric (Set.Ico 0 T)
  initial : metric 0 = g0
  source : ∀ (t : ℝ) (x : M),
    TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ
  gaugeCorrection : ∀ (t : ℝ) (x : M),
    TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ
  transportedEquation : ∀ (t : ℝ), t ∈ Set.Ico 0 T →
    ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s ↦ (metric s).inner x u v)
        (source t x u v - gaugeCorrection t x u v) (Set.Ico 0 T) t
  cancellation : ∀ (t : ℝ), t ∈ Set.Ico 0 T →
    ∀ (D : LeviCivitaData (metric t)) (x : M)
      (u v : TangentSpace (𝓡 n) x),
      source t x u v - gaugeCorrection t x u v = -2 * D.ricci x u v

theorem Certificate.equation
    {g0 : RiemannianMetric n M} (C : Certificate (n := n) (M := M) g0)
    (t : ℝ) (ht : t ∈ Set.Ico 0 C.T)
    (D : LeviCivitaData (C.metric t)) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (C.metric s).inner x u v)
      (-2 * D.ricci x u v) (Set.Ico 0 C.T) t := by
  rw [← C.cancellation t ht D x u v]
  exact C.transportedEquation t ht x u v

theorem Certificate.exists_metricFamily
    {g0 : RiemannianMetric n M} (C : Certificate (n := n) (M := M) g0) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (D : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D.ricci x u v) (Set.Ico 0 T) t := by
  refine ⟨C.T, C.hT, C.metric, C.initial, C.smooth, ?_⟩
  intro t ht D x u v
  exact C.equation t ht D x u v

end GaugeRecovery

end PoincareConjecture
