import Mathlib.Analysis.Calculus.ContDiff.Bounds










set_option autoImplicit false

open Set
open scoped ContDiff

variable {𝕜 E F G U V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]




theorem ContinuousLinearEquiv.norm_iteratedFDeriv_affine_le
    (L : E ≃L[𝕜] F) (f : F → G) (a x : E) (m : ℕ) :
    ‖iteratedFDeriv 𝕜 m (fun y => f (L (y - a))) x‖ ≤
      ‖iteratedFDeriv 𝕜 m f (L (x - a))‖ * ‖L.toContinuousLinearMap‖ ^ m := by
  have heq := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (mem_univ (L (x - a))) m
  simp only [preimage_univ, iteratedFDerivWithin_univ] at heq
  change ‖iteratedFDeriv 𝕜 m (fun y => (f ∘ L) (y - a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub, heq]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv 𝕜 m f (L (x - a))).norm_compContinuousLinearMap_le
      (fun _ : Fin m => L.toContinuousLinearMap)




theorem norm_iteratedFDeriv_bilinear_apply_const
    {f : E → U →L[𝕜] V →L[𝕜] G} {x : E} {N : ℕ∞ω}
    (hf : ContDiffAt 𝕜 N f x) {m : ℕ} (hm : m ≤ N) (u : U) (v : V) :
    ‖iteratedFDeriv 𝕜 m (fun y => f y u v) x‖ ≤
      ‖u‖ * ‖v‖ * ‖iteratedFDeriv 𝕜 m f x‖ := by
  calc
    _ ≤ ‖v‖ * ‖iteratedFDeriv 𝕜 m (fun y => f y u) x‖ :=
      norm_iteratedFDeriv_clm_apply_const (hf.clm_apply contDiffAt_const) hm
    _ ≤ ‖v‖ * (‖u‖ * ‖iteratedFDeriv 𝕜 m f x‖) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_clm_apply_const hf hm) (norm_nonneg v)
    _ = _ := by ring




theorem ContinuousLinearEquiv.norm_iteratedFDeriv_affine_bilinear_smul_le
    (L : E ≃L[𝕜] F) {f : F → U →L[𝕜] V →L[𝕜] G} (a x : E) (m : ℕ)
    (hf : ContDiffAt 𝕜 m f (L (x - a))) (c : 𝕜) (u : U) (v : V) :
    ‖iteratedFDeriv 𝕜 m (fun y => c • f (L (y - a)) u v) x‖ ≤
      ‖c‖ * ‖u‖ * ‖v‖ * ‖L.toContinuousLinearMap‖ ^ m *
        ‖iteratedFDeriv 𝕜 m f (L (x - a))‖ := by
  have he : ContDiffAt 𝕜 m (fun y => f y u v) (L (x - a)) :=
    (hf.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have h := L.norm_iteratedFDeriv_affine_le (fun y => c • f y u v) a x m
  rw [iteratedFDeriv_const_smul_apply' he, norm_smul] at h
  calc
    _ ≤ (‖c‖ * (‖u‖ * ‖v‖ * ‖iteratedFDeriv 𝕜 m f (L (x - a))‖)) *
        ‖L.toContinuousLinearMap‖ ^ m := h.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_bilinear_apply_const hf le_rfl u v) (norm_nonneg c))
          (pow_nonneg (norm_nonneg _) m))
    _ = _ := by ring
