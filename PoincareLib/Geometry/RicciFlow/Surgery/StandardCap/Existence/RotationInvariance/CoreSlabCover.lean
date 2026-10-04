import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.EndSlabCover

/-!
# The fixed core band and two physical end slabs

The exhaustion sublevel six is covered by its sublevel five and two
actual closed end slabs. The upper slab includes height five, as required
for both finite boundary energy comparisons. This is Morgan-Tian
Section 12.5, pp. 309-319 and core-energy-comparison-api.md.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- The fixed core band is covered by the core plateau and the two
physical end slabs, including the top boundary
(Section 12.5, pp. 309-319). -/
theorem endExhaustion_six_sublevel_cover
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g) :
    {x : StandardCapSpace | endExhaustion e x ≤ 6} ⊆
      ({x | endExhaustion e x ≤ 5} ∪ endClosedSlab e 4 (23 / 5)) ∪
        endClosedSlab e (22 / 5) 5 := by
  intro x hx
  change endExhaustion e x ≤ 6 at hx
  by_cases hcore : endExhaustion e x ≤ 5
  · exact Or.inl (Or.inl hcore)
  · obtain ⟨z, _, hzx, hvalue⟩ := endExhaustion_large_coordinate e (by linarith)
    have hl : 4 < z.2 := by linarith
    have hu : z.2 ≤ 5 := by linarith
    by_cases hlow : z.2 ≤ 23 / 5
    · exact Or.inl (Or.inr ⟨z, ⟨mem_univ _, hl.le, hlow⟩, hzx⟩)
    · exact Or.inr ⟨z, ⟨mem_univ _, by linarith, hu⟩, hzx⟩

end PoincareMT.M34
