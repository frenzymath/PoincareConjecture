/- Adapted from Mapher `PoincareMT/Proofs/M03/ShortTime.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Theory
import PoincareLib.Geometry.RicciFlow.Local.Connection.Existence
import PoincareLib.Geometry.RicciFlow.Local.Connection.CurvatureIndependence
import PoincareLib.Geometry.RicciFlow.Local.Energy.Comparison.GlobalDifferenceEnergy
import PoincareLib.Geometry.RicciFlow.Local.Energy.Comparison.UniquenessClosure
import PoincareLib.Geometry.RicciFlow.Local.Existence.FamilyEquation
import PoincareLib.Geometry.RicciFlow.Local.DeTurck.Construction.DeTurckResponseMetric

/-!
# Short-time Ricci-flow existence and uniqueness

Morgan-Tian, Theorem 3.11, printed pp. 39-40, supplies the analytic existence
and uniqueness obligations. The native DeTurck construction supplies the
metric family. The middle theorem assembles it with compatible-connection
existence into a Ricci flow. Uniqueness is the compact difference-energy
closure. For the DeTurck pullback sign, see MT-DETURCK-PULLBACK-SIGN in
`reviews/errata/2026-09-12-deturck-pullback.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

/-- Analytic existence of a smooth metric family satisfying the intrinsic Ricci equation. -/
theorem exists_ricciFlow_metricFamily (g0 : RiemannianMetric n M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (D : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D.ricci x u v) (Set.Ico 0 T) t := by
  exact DeTurckResponseMetricNative.exists_metricFamily g0

/-- Assemble a short-time flow from the analytic family and connection-existence obligations. -/
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

/-- Geometric uniqueness on compact manifolds with an included initial time. -/
theorem ricciFlowUniqueness : RicciFlowUniqueness n M := by
  exact RicciFlow.Local.ricciFlowUniqueness_of_difference_energy

end PoincareMT
