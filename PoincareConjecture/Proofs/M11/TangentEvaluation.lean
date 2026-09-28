import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

theorem derivative_apply_smooth_on_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {s : Set M} (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) (hs : IsOpen s) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun v : TangentBundle I M ↦ mfderiv I 𝓘(ℝ, F) f v.proj v.2)
      ((π E (TangentSpace I : M → Type _)) ⁻¹' s) := by
  have ht := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hs.uniqueMDiffOn
  have h := (contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F)).comp_contMDiffOn ht
  apply h.congr
  intro v hv
  change mfderiv I 𝓘(ℝ, F) f v.proj v.2 = mfderivWithin I 𝓘(ℝ, F) f s v.proj v.2
  rw [mfderivWithin_of_isOpen hs hv]

end PoincareConjecture.Proofs.M11
