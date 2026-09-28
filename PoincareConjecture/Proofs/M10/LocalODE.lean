import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike









set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem eventuallyEq_of_contDiffAt_vectorField {V : E → E} {f g : ℝ → E} {t₀ : ℝ}
    (hV : ContDiffAt ℝ 1 V (f t₀))
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (V (f t)) t)
    (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (V (g t)) t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨K, U, hU, hLip⟩ := hV.exists_lipschitzOnWith
  have hfU : ∀ᶠ t in 𝓝 t₀, f t ∈ U := hf.self_of_nhds.continuousAt hU
  have hgU : ∀ᶠ t in 𝓝 t₀, g t ∈ U :=
    hg.self_of_nhds.continuousAt (by simpa only [heq] using hU)
  exact ODE_solution_unique_of_eventually (v := fun _ ↦ V) (s := fun _ ↦ U)
    (Eventually.of_forall (fun _ ↦ hLip)) (hf.and hfU) (hg.and hgU) heq

end PoincareConjecture.M10
