import PoincareConjecture.Proofs.M14.Mathlib.RectanglePartialTangent
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

variable {𝕜 P F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {S : Set 𝕜} {U : Set P} {q : 𝕜 × P → F} {m k : ℕ∞ω}

theorem ContDiffOn.contDiffOn_derivWithin_fst_param (hq : ContDiffOn 𝕜 m q (S ×ˢ U))
    (hS : UniqueDiffOn 𝕜 S) (hU : UniqueDiffOn 𝕜 U) (hkm : k + 1 ≤ m) :
    ContDiffOn 𝕜 k (fun z => derivWithin (fun r => q (r, z.2)) S z.1) (S ×ˢ U) := by
  have hM : ContMDiffOn ((𝓘(𝕜, 𝕜)).prod (𝓘(𝕜, P))) 𝓘(𝕜, F) m q (S ×ˢ U) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hq.contMDiffOn
  have htan := hM.contMDiffOn_partialTangentWithin_fst_prod hS hU (1 : 𝕜) hkm
  have h := (contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F) (n := k)).comp_contMDiffOn htan
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  convert h.contDiffOn using 1
  funext z
  simp only [Function.comp_def, mfderivWithin_eq_fderivWithin, derivWithin]
  rfl

theorem ContDiffOn.exists_uniform_derivWithin_bound_fst
    (hq : ContDiffOn 𝕜 ∞ q (S ×ˢ U)) (hS : UniqueDiffOn 𝕜 S)
    (hSc : IsCompact S) (hU : IsOpen U) {K : Set P}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ W ∈ K, ∀ r ∈ S,
      ‖derivWithin (fun t => q (t, W)) S r‖ ≤ M := by
  have hd := hq.contDiffOn_derivWithin_fst_param hS hU.uniqueDiffOn
    (k := ∞) (by simp)
  obtain ⟨M, hM⟩ := (hSc.prod hK).exists_bound_of_continuousOn
    (hd.continuousOn.mono (fun _ hz => ⟨hz.1, hKU hz.2⟩))
  exact ⟨max M 0, le_max_right _ _, fun W hW r hr =>
    (hM (r, W) ⟨hr, hW⟩).trans (le_max_left _ _)⟩
