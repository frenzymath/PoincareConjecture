import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v w

namespace PoincareConjecture.M63

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

theorem smooth_retraction_differentials [IsManifold 𝓘(ℝ, E) ∞ M] {e : M → V}
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ e) {U : Set V} (hU : IsOpen U)
    (heU : range e ⊆ U) {ρ : V → M}
    (hρ : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p) :
    ContDiffOn ℝ ∞ (e ∘ ρ) U ∧
    (∀ z ∈ U, ∀ v : V, fderiv ℝ (e ∘ ρ) z v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) e (ρ z) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ρ z v)) ∧
    ∀ p : M, ∀ v : TangentSpace 𝓘(ℝ, E) p,
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ρ (e p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) e p v) = v := by
  refine ⟨(he.comp_contMDiffOn hρ).contDiffOn, ?_, ?_⟩
  · intro z hz v
    have hchain : fderiv ℝ (e ∘ ρ) z =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) e (ρ z)).comp
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ρ z) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp z (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hρ.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp))
    exact congrArg (fun L : V →L[ℝ] V => L v) hchain
  · intro p v
    have hchain := mfderiv_comp p
      ((hρ.contMDiffAt (hU.mem_nhds (heU (mem_range_self p)))).mdifferentiableAt (by simp))
      (he.mdifferentiable (by simp)).mdifferentiableAt
    have heq : ρ ∘ e = id := funext hρe
    rw [heq, mfderiv_id] at hchain
    exact (congrArg (fun L : E →L[ℝ] E => L v) hchain).symm

end PoincareConjecture.M63
