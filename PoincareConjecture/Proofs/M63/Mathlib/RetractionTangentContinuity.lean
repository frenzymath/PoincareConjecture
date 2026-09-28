import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff

universe u v w z

namespace PoincareConjecture.M63

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {Z : Type z} [TopologicalSpace Z]

theorem continuousOn_tangentSection_of_retraction_pushforward
    {e : M → V} (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ e)
    {U : Set V} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : V → M}
    (hρ : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {s : Set Z} (p : Z → M) (Y : ∀ z, TangentSpace 𝓘(ℝ, E) (p z))
    (hp : ContinuousOn p s)
    (hY : ContinuousOn (fun z => (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) e (p z) (Y z) : V)) s) :
    ContinuousOn (fun z => (⟨p z, Y z⟩ : TangentBundle 𝓘(ℝ, E) M)) s := by
  let T : Z → TangentBundle 𝓘(ℝ, V) V := fun z =>
    ⟨e (p z), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) e (p z) (Y z)⟩
  have hT : ContinuousOn T s :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, V)).symm.continuous.comp_continuousOn
      ((he.continuous.comp_continuousOn hp).prodMk hY)
  have hr := hρ.continuousOn_tangentMapWithin (by simp) hU.uniqueMDiffOn
  have hcomp := hr.comp hT (fun z _ => heU (mem_range_self (p z)))
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  apply hcomp.congr
  intro z _
  dsimp only [Function.comp_def, T, tangentMapWithin]
  rw [mfderivWithin_of_isOpen hU (heU (mem_range_self (p z)))]
  symm
  apply Bundle.TotalSpace.ext (hρe (p z))
  apply heq_of_eq
  exact hleft (p z) (Y z)

end PoincareConjecture.M63
