import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M32

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_stationary_smooth_sphere_isotopy {U S₀ S₁ : Set M}
    (h : SmoothSphereIsotopicIn U S₀ S₁) :
    ∃ F : ℝ × UnitTwoSphere → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ F ∧
      (∀ t : ℝ, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => F (t, q))) ∧
      (∀ t : ℝ, range (fun q => F (t, q)) ⊆ U) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ q, F (t, q) = F (0, q)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ q, F (t, q) = F (1, q)) ∧
      range (fun q => F (0, q)) = S₀ ∧ range (fun q => F (1, q)) = S₁ := by
  obtain ⟨H, hH, hembed, hzero, hone⟩ := h
  let F : ℝ × UnitTwoSphere → M := fun z => H (Real.smoothTransition z.1, z.2)
  have htime (t : ℝ) : Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  refine ⟨F, ?_, (fun t => (hembed _ (htime t)).1),
    (fun t => (hembed _ (htime t)).2), ?_, ?_, ?_, ?_⟩
  · exact hH.comp_contMDiff
      ((Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
      (fun z => ⟨htime z.1, mem_univ _⟩)
  · intro t ht q
    simp only [F, Real.smoothTransition.zero_of_nonpos ht, Real.smoothTransition.zero]
  · intro t ht q
    simp only [F, Real.smoothTransition.one_of_one_le ht, Real.smoothTransition.one]
  · simpa only [F, Real.smoothTransition.zero] using hzero
  · simpa only [F, Real.smoothTransition.one] using hone

end PoincareConjecture.M32
