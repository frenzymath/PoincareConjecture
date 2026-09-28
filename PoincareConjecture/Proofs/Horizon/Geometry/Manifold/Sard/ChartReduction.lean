import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sard.RegularValue
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold

open Poincare.Analysis



theorem manifold_criticalImage_null_of_euclidean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (hEuclidean : ∀ (V : Set E) (g : E → ℝ), IsOpen V →
      ContDiffOn ℝ ∞ g V →
      volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [SecondCountableTopology M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    volume (f '' {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}) = 0 := by
  let C : Set M := {x | ¬ Function.Surjective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)}
  have hlocal (a : M) : volume (f '' (C ∩ (chartAt E a).source)) = 0 := by
    let e := chartAt E a
    let g : E → ℝ := f ∘ e.symm
    have he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target :=
      contMDiffOn_chart_symm
    have hg : ContDiffOn ℝ ∞ g e.target :=
      (hf.comp_contMDiffOn he).contDiffOn
    apply measure_mono_null _ (hEuclidean e.target g e.open_target hg)
    rintro y ⟨x, ⟨hxC, hxe⟩, rfl⟩
    refine ⟨e x, ⟨e.map_source hxe, ?_⟩, ?_⟩
    · have heAt := (he (e x) (e.map_source hxe)).contMDiffAt
        (e.open_target.mem_nhds (e.map_source hxe))
      have hchain : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g (e x) =
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (e.symm (e x))).comp
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
        exact mfderiv_comp (e x) (hf.mdifferentiable (by simp) (e.symm (e x)))
          (heAt.mdifferentiableAt (by simp))
      have hnot : ¬ Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g (e x)) := by
        rw [hchain]
        intro hsurj
        have hcritical : e.symm (e x) ∈ C := (e.left_inv hxe).symm ▸ hxC
        apply hcritical
        intro z
        obtain ⟨v, hv⟩ := hsurj z
        exact ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) v, hv⟩
      change ¬ Function.Surjective (fderiv ℝ g (e x))
      rw [mfderiv_eq_fderiv] at hnot
      exact hnot
    · exact congrArg f (e.left_inv hxe)
  obtain ⟨S, hS, hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : M => (chartAt E x).open_source.mem_nhds (mem_chart_source E x))
  have hnull : volume (⋃ a ∈ S, f '' (C ∩ (chartAt E a).source)) = 0 :=
    (measure_biUnion_null_iff hS).mpr (fun a _ => hlocal a)
  apply measure_mono_null _ hnull
  rintro y ⟨x, hx, rfl⟩
  have hxc : x ∈ ⋃ a ∈ S, (chartAt E a).source := hcover.symm ▸ mem_univ x
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxc
  exact mem_iUnion₂.mpr ⟨a, ha, ⟨x, ⟨hx, hxa⟩, rfl⟩⟩

end Poincare.Manifold
