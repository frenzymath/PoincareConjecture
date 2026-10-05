import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import Mathlib.Logic.Equiv.Sum

/-!
# Retained actual slices for the ordinary Chapter 11 realization

The supplied ordinary product already has the actual time fibers, with
their selected charts, metrics and compatible connections. Their dependent
sum is equivalent to the original spacetime. In particular, excluded times
have empty fibers. Source: Morgan-Tian Theorems 12.28-12.29, pp. 323-325;
the ordinary Chapter 11 derivation in the M34 task records.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric 3 M}

/-- The Chapter 11 slice retains all structures of the supplied actual
time fiber (Theorem 12.28, pp. 323-324). -/
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

/-- These retained slices are inhabited exactly on the actual ordinary
flow interval (Theorem 12.28, pp. 323-324). -/
theorem ordinaryChapter11Slice_nonempty (R : OrdinaryProductSpacetimeConclusion g I)
    (t : ℝ) : Nonempty (ordinaryChapter11Slice R t).carrier ↔ t ∈ I.domain := by
  rw [← R.spacetime.time_range]
  constructor
  · rintro ⟨x⟩
    exact ⟨x.val, x.property⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩

/-- Flattening the actual time fibers gives the original ordinary
spacetime carrier (Theorem 12.28, pp. 323-324). -/
def ordinaryChapter11Flatten (R : OrdinaryProductSpacetimeConclusion g I) :
    (Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) ≃ R.spacetime.Point :=
  Equiv.sigmaFiberEquiv R.spacetime.timeFunction

/-- The dependent sum carries the actual spacetime topology transported
by flattening its time fibers (Theorem 12.28, pp. 323-324). -/
@[instance_reducible] def ordinaryChapter11Topology
    (R : OrdinaryProductSpacetimeConclusion g I) :
    TopologicalSpace (Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) :=
  TopologicalSpace.induced (ordinaryChapter11Flatten R) inferInstance

/-- Flattening is a homeomorphism for the specified spacetime topology
(Theorem 12.28, pp. 323-324). -/
def ordinaryChapter11Homeomorph (R : OrdinaryProductSpacetimeConclusion g I) :
    letI := ordinaryChapter11Topology R
    (Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) ≃ₜ R.spacetime.Point := by
  letI := ordinaryChapter11Topology R
  exact (ordinaryChapter11Flatten R).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The dependent time label equals the physical clock under the actual
spacetime homeomorphism (Theorem 12.28, pp. 323-324). -/
theorem ordinaryChapter11Flatten_clock (R : OrdinaryProductSpacetimeConclusion g I)
    (z : Σ t : ℝ, (ordinaryChapter11Slice R t).carrier) :
    R.spacetime.timeFunction (ordinaryChapter11Flatten R z) = z.1 := z.2.property

end PoincareMT.M34
