import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Pullback









set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt
    (L : G →L[ℝ] E) {f : E → F} {x : G}
    (hf : ContDiffAt ℝ ∞ f (L x)) (m : ℕ) :
    iteratedFDeriv ℝ m (f ∘ L) x =
      (iteratedFDeriv ℝ m f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω))
    (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp hs
  have hpre := hvo.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right (hfs.mono hv)
    hvo.uniqueDiffOn hpre.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hpre hxv,
    iteratedFDerivWithin_of_isOpen _ hvo hxv] using h



theorem locallyEventuallyBoundedDerivatives_comp_continuousLinearMap
    {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E)
    {U : Set E} (hU : IsOpen U) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hmap : MapsTo L Ω U) {f : ℕ → E → F}
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) U)
    (hbound : ∀ K, IsCompact K → K ⊆ U → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f k) x‖ ≤ B) :
    LocallyEventuallyBoundedDerivatives Ω (fun k => f k ∘ L) := by
  intro K hK hKΩ m
  obtain ⟨B, hB⟩ := hbound (L '' K) (hK.image L.continuous)
    (image_subset_iff.mpr (fun x hx => hmap (hKΩ hx))) m
  refine ⟨B * ∏ _ : Fin m, ‖L‖, ?_⟩
  filter_upwards [hB] with k hk x hx
  rw [iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L
    ((hf k).contDiffAt (hU.mem_nhds (hmap (hKΩ hx)))) m]
  exact ((iteratedFDeriv ℝ m (f k) (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => L)).trans
      (mul_le_mul_of_nonneg_right (hk (L x) (mem_image_of_mem L hx))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem smooth_convergence_comp_continuousLinearMap
    (L : G →L[ℝ] E) {U : Set E} (hU : IsOpen U)
    {f : ℕ → E → F} {f₀ : E → F} (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m f₀) atTop K) :
    (∀ x ∈ L ⁻¹' U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ L) W) ∧
      ∀ m K, IsCompact K → K ⊆ L ⁻¹' U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f k ∘ L))
        (iteratedFDeriv ℝ m (f₀ ∘ L)) atTop K := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨W, hW, hxW, hks⟩ := hlocal (L x) hx
    exact ⟨L ⁻¹' W, hW.preimage L.continuous, hxW,
      hks.mono fun _ hk => hk.comp_continuousLinearMap L⟩
  · intro m K hK hKU
    have hI := hK.image L.continuous
    have hIU : L '' K ⊆ U := image_subset_iff.mpr hKU
    have hcomp := ((hjet m (L '' K) hI hIU).comp L).mono (subset_preimage_image L K)
    have h := (ContinuousMultilinearMap.compContinuousLinearMapL
      (F := F) (fun _ : Fin m => L)).uniformContinuous.comp_tendstoUniformlyOn hcomp
    apply (h.congr ?_).congr_right ?_
    · filter_upwards [eventually_contDiffAt_on_compact hI hIU hlocal] with k hk x hx
      exact (iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L
        (hk (L x) (mem_image_of_mem L hx)) m).symm
    · intro x hx
      exact (iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L
        (hf₀.contDiffAt (hU.mem_nhds (hKU hx))) m).symm

end Poincare.Analysis.Calculus
