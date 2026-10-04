import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.AreaObstruction

/-! # The limiting level-area contradiction -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RiemannianMetric

variable {N : Type*} [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N]
  [T3Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N] [CompactSpace N] [Nonempty N]

/-- Subunit scalar curvature and expanding area cannot converge to the
area of a unit-scalar metric on the same compact surface. -/
theorem false_of_subunit_scalar_nondecreasing_area_limit
    (g : RiemannianMetric 2 N) (h : ℕ → RiemannianMetric 2 N)
    (hunit : ∀ x, g.leviCivitaData.scalarCurvature x = 1)
    (hsubunit : ∀ x, (h 0).leviCivitaData.scalarCurvature x < 1)
    (harea : ∀ k, (h 0).volumeMeasure.real univ ≤ (h k).volumeMeasure.real univ)
    (hlimit : Tendsto (fun k => (h k).volumeMeasure.real univ) atTop
      (𝓝 (g.volumeMeasure.real univ))) : False := by
  have hstrict := g.leviCivitaData.volume_lt_of_unit_scalar_and_subunit_scalar
    (h 0).leviCivitaData hunit hsubunit
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
    (Filter.Eventually.of_forall harea)
  exact hstrict.not_ge hle

end PoincareMT.RiemannianMetric
