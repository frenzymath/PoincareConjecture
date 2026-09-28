import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Basic









set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff





theorem contDiffOn_one_uncurry_of_partials
    {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {S : Set (E₁ × E₂)} (hS : IsOpen S) {f : E₁ → E₂ → F}
    {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} {f₂ : E₁ → E₂ → E₂ →L[𝕜] F}
    (h₁ : ContinuousOn (Function.uncurry f₁) S)
    (h₂ : ContinuousOn (Function.uncurry f₂) S)
    (hd₁ : ∀ p ∈ S, HasFDerivAt (fun x => f x p.2) (f₁ p.1 p.2) p.1)
    (hd₂ : ∀ p ∈ S, HasFDerivAt (f p.1) (f₂ p.1 p.2) p.2) :
    ContDiffOn 𝕜 1 (Function.uncurry f) S := by
  let D : (E₁ × E₂) → (E₁ × E₂) →L[𝕜] F :=
    fun p => (f₁ p.1 p.2).coprod (f₂ p.1 p.2)
  have hD : ContinuousOn D S := h₁.continuousLinearMapCoprod h₂
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := 0) hS.uniqueDiffOn).mpr
  refine ⟨by simp, D, contDiffOn_zero.mpr hD, ?_⟩
  intro p hp
  have hmem : ∀ᶠ q in 𝓝 p, q ∈ S := hS.mem_nhds hp
  have he₁ : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun x => f x q.2) (f₁ q.1 q.2) q.1 :=
    hmem.mono (fun q hq => hd₁ q hq)
  have he₂ : ∀ᶠ q in 𝓝 p, HasFDerivAt (f q.1) (f₂ q.1 q.2) q.2 :=
    hmem.mono (fun q hq => hd₂ q hq)
  exact (hasStrictFDerivAt_uncurry_coprod he₁ he₂
    (h₁.continuousAt (hS.mem_nhds hp)) (h₂.continuousAt (hS.mem_nhds hp))).hasFDerivAt
      |>.hasFDerivWithinAt
