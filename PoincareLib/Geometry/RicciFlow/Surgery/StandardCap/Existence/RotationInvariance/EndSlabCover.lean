import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.EndCompactSlabs

/-!
# The fixed three-slab cover of the end cutoff

The actual closed end slabs respect interval inclusion. Their central
plateau contains the three translated target slabs, and three overlapping
source slabs cover the cutoff support. This is the fixed geometry in
Morgan-Tian Section 12.5, pp. 309-319 and end-overlap-energy.md.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)

/-- Inclusion of height intervals gives inclusion of the actual closed
slabs (Section 12.5, pp. 309-319). -/
theorem endClosedSlab_mono {a b c d : ℝ} (hac : c ≤ a) (hbd : b ≤ d) :
    endClosedSlab e a b ⊆ endClosedSlab e c d := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨mem_univ _, hac.trans hz.2.1, hz.2.2.trans hbd⟩, rfl⟩

/-- The cutoff is identically one on the fixed closed central slab
(Section 12.5, pp. 309-319). -/
theorem endEnergyCutoff_eq_one_on_slab {x : StandardCapSpace}
    (hx : x ∈ endClosedSlab e (17 / 5) (23 / 5)) : endEnergyCutoff e x = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hl : (17 / 5 : ℝ) ≤ z.2 := hz.2.1
  have hu : z.2 ≤ (23 / 5 : ℝ) := hz.2.2
  apply endEnergyCutoff_eq_one e
  rw [endExhaustion_coordinate_of_two_le e (by linarith)]
  constructor <;> linarith

/-- Three fixed closed slabs cover the actual cutoff support, including
its boundary (Section 12.5, pp. 309-319). -/
theorem endEnergyCutoff_tsupport_subset_three_slabs :
    tsupport (endEnergyCutoff e) ⊆
      (endClosedSlab e (31 / 10) (18 / 5) ∪ endClosedSlab e (17 / 5) (23 / 5)) ∪
        endClosedSlab e (22 / 5) (49 / 10) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := endEnergyCutoff_tsupport_subset_slab e hx
  have hl : (31 / 10 : ℝ) ≤ z.2 := hz.2.1
  have hu : z.2 ≤ (49 / 10 : ℝ) := hz.2.2
  by_cases hlow : z.2 ≤ 18 / 5
  · exact Or.inl (Or.inl ⟨z, ⟨mem_univ _, hl, hlow⟩, rfl⟩)
  · by_cases hmid : z.2 ≤ 23 / 5
    · exact Or.inl (Or.inr ⟨z, ⟨mem_univ _, by linarith, hmid⟩, rfl⟩)
    · exact Or.inr ⟨z, ⟨mem_univ _, by linarith, hu⟩, rfl⟩

end PoincareMT.M34
