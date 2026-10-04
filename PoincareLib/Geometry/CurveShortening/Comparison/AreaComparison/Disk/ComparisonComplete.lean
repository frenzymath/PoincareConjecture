import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Annulus.Reflection
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Disk.GluingFromAnnulus
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Projection.Complete

/-!
# Disk comparison from the actual projected annulus

The projected annulus supplies a Lipschitz collar in each direction.
Both estimates begin with an arbitrary supplied disk, and the guarded
filling-area infima follow from the two estimates.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Project the supplied product annulus and construct both disk comparisons without an
additional geometric certificate. Source: Auxiliary step for MT Lemma 19.30, p. 462; the
actual half-disk collar in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64DiskAreaComparison_of_product
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference) (t : ℝ) :
    M64DiskAreaComparison P t := by
  intro c0 c1 A gamma0 gamma1 h0 h1
  obtain ⟨_, B, _, harea, _, _⟩ := m64ProjectedAnnulus_of_annulus P t c0 c1 A
  apply m64DiskGluingConclusion_of_estimates P t A gamma0 gamma1
  · intro eta heta D0
    obtain ⟨D1, hD1⟩ := m64DiskGluing_of_annulus B gamma0 gamma1 h0 h1 D0
    rw [harea] at hD1
    exact ⟨D1, by linarith⟩
  · intro eta heta D1
    obtain ⟨D0, hD0⟩ := m64DiskGluing_of_annulus
      (m64Annulus_reverse B) gamma1 gamma0 h1 h0 D1
    rw [m64Annulus_reverse_area, harea] at hD0
    exact ⟨D0, by linarith⟩

end PoincareMT
