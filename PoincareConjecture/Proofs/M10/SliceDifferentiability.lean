import PoincareConjecture.Proofs.M10.Countability
import PoincareConjecture.Proofs.M10.ChartFunctionLipschitz
import PoincareConjecture.Proofs.M10.Rademacher
import PoincareConjecture.Proofs.M10.SliceLipschitz









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}


theorem reducedLength_slice_nondifferentiability_eq_zero
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (p : M)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    calibratedMetricVolume (F.metric (T - τ))
      {q | ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
        (fun x ↦ reducedLength F T p x τ) q} = 0 := by
  obtain ⟨G⟩ := hDifferential.exponential_geometry p
  let : SecondCountableTopology M := secondCountableTopology_of_exponential hL G hτ hmax
  apply calibratedMetricVolume_nondifferentiability_eq_zero (F.metric (T - τ))
  exact locallyLipschitz_in_coordinates (F.metric T)
    (reducedLength_slice_locallyLipschitz hL hDifferential hwindow p hτ hmax)

end PoincareConjecture.M10
