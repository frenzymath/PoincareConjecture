import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Statements.M12GeneralizedEquation
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric 3 M}

def ordinaryChapter11Slice (R : OrdinaryProductSpacetimeConclusion g I) (t : ℝ) :
    GeneralizedSliceCarrier where
  carrier := (R.slices t).Point
  topologicalSpace := inferInstance
  measurableSpace := (R.slices t).measurableSpace
  borelSpace := (R.slices t).borelSpace
  chartedSpace := (R.slices t).chartedSpace
  isManifold := (R.slices t).isManifold
  t2Space := by
    let : T2Space R.spacetime.Point := R.spacetime.t2Space
    exact (R.slices t).inclusion_embedding.t2Space
  t3Space := (R.slices t).t3Space
  secondCountable := (R.slices t).secondCountable

theorem ordinaryChapter11Slice_nonempty (R : OrdinaryProductSpacetimeConclusion g I)
    (t : ℝ) : Nonempty (ordinaryChapter11Slice R t).carrier ↔ t ∈ I.domain := by
  rw [← R.spacetime.time_range]
  constructor
  · rintro ⟨x⟩
    exact ⟨x.val, x.property⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩

def ordinaryChapter11Flatten (R : OrdinaryProductSpacetimeConclusion g I) :
    (Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) ≃ R.spacetime.Point :=
  Equiv.sigmaFiberEquiv R.spacetime.timeFunction

@[instance_reducible] def ordinaryChapter11Topology
    (R : OrdinaryProductSpacetimeConclusion g I) :
    TopologicalSpace (Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) :=
  TopologicalSpace.induced (ordinaryChapter11Flatten R) inferInstance

def ordinaryChapter11Homeomorph (R : OrdinaryProductSpacetimeConclusion g I) :
    letI := ordinaryChapter11Topology R
    (Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) ≃ₜ R.spacetime.Point := by
  letI := ordinaryChapter11Topology R
  exact (ordinaryChapter11Flatten R).toHomeomorphOfIsInducing ⟨rfl⟩

theorem ordinaryChapter11Flatten_clock (R : OrdinaryProductSpacetimeConclusion g I)
    (z : Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) :
    R.spacetime.timeFunction (ordinaryChapter11Flatten R z) = z.1 := z.2.property

end PoincareConjecture.M34
