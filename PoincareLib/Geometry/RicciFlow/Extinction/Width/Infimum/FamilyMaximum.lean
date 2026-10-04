import PoincareLib.Geometry.RicciFlow.Extinction.Width.Infimum.SphereCompactness
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Theory
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Theory
import Mathlib.Topology.Order.Compact

/-!
# The maximum filling area of a sphere family

Morgan--Tian Definition 18.17, printed p. 430: M60 filling continuity on
null loops and compactness of the parameter sphere identify the actual
real supremum with an attained nonnegative maximum.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- M60's filling service gives the family maximum of Definition 18.17, p. 430. -/
theorem m61FamilyWidth_from_M60
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (P60 : M60FillingAreaProperties g)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily F) : M61FamilyWidthProperties g F := by
  have hcontinuous : Continuous (fun c => fillingArea g (F c)) :=
    P60.continuous_on_null_loops.comp_continuous F.continuous hnull
  obtain ⟨c, _, hc⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set LoopTwoSphere).Nonempty)
    hcontinuous.continuousOn
  have hgreatest : IsGreatest (Set.range (fun c => fillingArea g (F c)))
      (fillingArea g (F c)) := by
    refine ⟨⟨c, rfl⟩, ?_⟩
    rintro _ ⟨d, rfl⟩
    exact hc (Set.mem_univ d)
  have hwidth : m61FamilyWidth g F = fillingArea g (F c) := hgreatest.csSup_eq
  exact
    { area_continuous := hcontinuous
      bounded_above := ⟨fillingArea g (F c), hgreatest.2⟩
      attained := ⟨c, hwidth.symm⟩
      nonnegative := hwidth.symm ▸ P60.nonnegative (F c) (hnull c) }

end PoincareMT
