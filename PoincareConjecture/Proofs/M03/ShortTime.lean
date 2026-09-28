import PoincareConjecture.Statements.Ch03.ShortTime
import PoincareConjecture.Proofs.M03.ConnectionExistence
import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.M03.GlobalDifferenceEnergy
import PoincareConjecture.Proofs.M03.UniquenessClosure
import PoincareConjecture.Proofs.M03.Existence.FamilyEquation
import PoincareConjecture.Proofs.M03.Existence.DeTurckResponseMetricNative

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

theorem exists_ricciFlow_metricFamily (g0 : RiemannianMetric n M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (D : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D.ricci x u v) (Set.Ico 0 T) t := by
  exact DeTurckResponseMetricNative.exists_metricFamily g0

theorem shortTimeRicciFlowExistence : ShortTimeRicciFlowExistence n M := by
  intro g0
  obtain ⟨T, hT, g, hg0, hsm, heq⟩ := exists_ricciFlow_metricFamily g0
  obtain ⟨D⟩ : Nonempty ((t : ℝ) → LeviCivitaData (g t)) :=
    ⟨fun t ↦ Classical.choice (exists_leviCivitaData (g t))⟩
  obtain ⟨s, hs0, hsT⟩ := exists_between hT
  exact ⟨T, hT, {
    metric := g
    connection := D
    interval := Set.ordConnected_Ico
    nontrivial := ⟨0, ⟨le_rfl, hT⟩, s, ⟨hs0.le, hsT⟩, ne_of_lt hs0⟩
    smooth := hsm
    equation := fun t ht x u v ↦ heq t ht (D t) x u v
  }, hg0⟩

theorem ricciFlowUniqueness : RicciFlowUniqueness n M := by
  exact Proofs.M03.ricciFlowUniqueness_of_difference_energy

end PoincareConjecture
