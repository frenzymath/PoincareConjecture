import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.AnnulusReflection
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.DiskGluingFromAnnulus
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionComplete

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

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

end PoincareConjecture
