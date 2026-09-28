import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.RegularScalar
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option backward.isDefEq.respectTransparency false

open Poincare.Analysis Set Function
open scoped Topology ContDiff Manifold





namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_manifold_superlevel_chart {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : M)
    (hreg : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f a)) :
    let L : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f a
    ∃ e : OpenPartialHomeomorph M (ℝ × L.ker),
      a ∈ e.source ∧ e a = (f a, 0) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × L.ker) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × L.ker) 𝓘(ℝ, E) ∞ e.symm e.target ∧
      (∀ x ∈ e.source, (e x).1 = f x) ∧
      ∀ c : ℝ, e '' (e.source ∩ {x | c ≤ f x}) = e.target ∩ {y | c ≤ y.1} := by
  dsimp only
  let φ := chartAt E a
  let g : E → ℝ := f ∘ φ.symm
  have hg : ContDiffOn ℝ ∞ g φ.target :=
    (hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)))).contDiffOn
  have hder : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f a = fderiv ℝ g (φ a) := by
    rw [(hf.mdifferentiable (by simp) a).mfderiv]
    simp [writtenInExtChartAt, extChartAt, g, φ, fderivWithin_univ, chartAt_self_eq]
  rw [hder] at hreg ⊢
  obtain ⟨e0, ha0, heV, he0a, he0, he0inv, he0f, he0level⟩ :=
    exists_smooth_superlevel_chart φ.open_target hg
      (φ.map_source (mem_chart_source E a)) hreg
  let e := φ.trans e0
  have hea : a ∈ e.source := ⟨mem_chart_source E a, ha0⟩
  have hefirst : ∀ x ∈ e.source, (e x).1 = f x := by
    intro x hx
    change (e0 (φ x)).1 = f x
    rw [he0f (φ x) (show φ x ∈ e0.source from hx.2)]
    change f (φ.symm (φ x)) = f x
    rw [φ.left_inv hx.1]
  refine ⟨e, hea, ?_, ?_, ?_, hefirst, ?_⟩
  · change e0 (φ a) = (f a, 0)
    simpa [g, φ] using he0a
  · exact he0.contMDiffOn.comp
      ((contMDiffOn_chart (I := 𝓘(ℝ, E))).mono (fun x hx => hx.1))
      (fun x hx => hx.2)
  · exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E))).comp
      (he0inv.contMDiffOn.mono (fun y hy => hy.1)) (fun y hy => hy.2)
  · intro c
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hcx⟩, rfl⟩
      exact ⟨e.map_source hx, by simpa [hefirst x hx] using hcx⟩
    · rintro ⟨hy, hcy⟩
      refine ⟨e.symm y, ⟨e.map_target hy, ?_⟩, e.right_inv hy⟩
      change c ≤ f (e.symm y)
      rw [← hefirst _ (e.map_target hy), e.right_inv hy]
      exact hcy



theorem frontier_superlevel_eq_regular_level {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (c : ℝ)
    (hc : ∀ x, f x = c → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)) :
    frontier {x | c ≤ f x} = {x | f x = c} := by
  apply Subset.antisymm
  · intro x hx
    exact (frontier_le_subset_eq continuous_const hf.continuous hx).symm
  · intro x hx
    obtain ⟨e, hxe, hea, he, hei, hef, helevel⟩ :=
      exists_manifold_superlevel_chart hf x (hc x hx)
    have himg := OpenPartialHomeomorph.IsImage.of_image_eq (helevel c)
    apply (himg.frontier.apply_mem_iff hxe).mp
    let L : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x
    have hhalf : {y : ℝ × L.ker | c ≤ y.1} = Ici c ×ˢ univ := by
      ext y
      simp
    rw [hhalf, frontier_prod_univ_eq, frontier_Ici]
    exact ⟨by simpa [hea] using hx, mem_univ _⟩


end Poincare.Manifold
