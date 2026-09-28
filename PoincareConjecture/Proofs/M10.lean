import PoincareConjecture.Statements.Ch06.ReducedVolume
import PoincareConjecture.Proofs.M09
import PoincareConjecture.Proofs.M10.WeakInequalities
import PoincareConjecture.Proofs.M10.MinimumBound
import PoincareConjecture.Proofs.M10.VolumeComparison
import PoincareConjecture.Proofs.M10.VolumePositive
import PoincareConjecture.Proofs.M10.RestrictedVolume
import PoincareConjecture.Proofs.M10.EuclideanRigidity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]

theorem reducedVolumeMonotonicity
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax) :
    Nonempty (ReducedVolumeTheory F T τmax) := by
  let G (p : M) := Classical.choice (hDifferential.exponential_geometry p)
  exact ⟨{
    measure_regularity := M10.reducedLength_measure_regularity hL hDifferential hwindow
    weak_inequalities := M10.reducedLength_weak_inequalities hL hDifferential hwindow
    minimum_bound := fun p _ hτ hmax ↦
      M10.reducedLength_minimum_bound hL hDifferential hT hwindow hcurvature p hτ hmax
    density_integrable := fun p _ hτ hmax ↦
      M10.reducedVolumeDensity_integrable hL hDifferential (G p) hτmax hT hwindow
        hcurvature hτ hmax
    volume_bounds := fun p _ hτ hmax ↦
      ⟨M10.reducedVolume_pos hL hDifferential (G p) hτmax hT hwindow hcurvature hτ hmax,
        M10.reducedVolume_le_euclidean hL hDifferential (G p) hτmax hT hwindow
          hcurvature hτ hmax⟩
    monotone := fun p ↦
      M10.reducedVolume_antitoneOn hL hDifferential (G p) hτmax hT hwindow hcurvature
    zero_time_limit := fun p ↦
      M10.reducedVolume_tendsto_zero hL hDifferential (G p) hτmax hT hwindow hcurvature
    open_domain_monotone := fun p _ hA ↦
      M10.reducedVolumeOn_antitoneOn hL hDifferential (G p) hτmax hT hwindow hcurvature hA
    euclidean_rigidity := fun p _ hτ hmax heq ↦
      M10.staticEuclideanFlowOn_of_reducedVolume_eq hL hDifferential (G p) hτmax hT
        hwindow hcurvature hτ hmax heq }⟩

theorem reducedVolumeMonotonicity_from_M08_M09
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)) :
    Nonempty (ReducedVolumeTheory F T τmax) := by
  rcases lGeodesicExistenceAndVariation_from_M04 F T τmax hT hτmax hwindow hcurvature with ⟨hL⟩
  rcases reducedLengthDifferentialInequalities_from_M04_M08 F T τmax
      hT hτmax hwindow hcurvature with ⟨hDifferential⟩
  exact reducedVolumeMonotonicity F T τmax hT hτmax hwindow hcurvature hL hDifferential

end PoincareConjecture
