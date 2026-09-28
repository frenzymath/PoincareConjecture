import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_global_smooth_sphere_isotopy {U S₀ S₁ : Set M}
    (h : SmoothSphereIsotopicIn U S₀ S₁) :
    ∃ H : ℝ × UnitTwoSphere → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H ∧
      (∀ t : ℝ, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => H (t, q)) ∧
        range (fun q => H (t, q)) ⊆ U) ∧
      range (fun q => H (0, q)) = S₀ ∧ range (fun q => H (1, q)) = S₁ := by
  obtain ⟨H, hH, hslice, hzero, hone⟩ := h
  let H' : ℝ × UnitTwoSphere → M := fun p => H (Real.smoothTransition p.1, p.2)
  have htime : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun p : ℝ × UnitTwoSphere => (Real.smoothTransition p.1, p.2)) :=
    (Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hH' : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H' :=
    hH.comp_contMDiff htime (fun p =>
      ⟨⟨Real.smoothTransition.nonneg p.1, Real.smoothTransition.le_one p.1⟩, mem_univ _⟩)
  refine ⟨H', hH', ?_, ?_, ?_⟩
  · intro t
    exact hslice (Real.smoothTransition t)
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  · simpa only [H', Real.smoothTransition.zero] using hzero
  · simpa only [H', Real.smoothTransition.one] using hone

end PoincareConjecture.M28
