import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmallGermExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmallPerturbation

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_identity_germ_isotopy (f : E → E) {U : Set E}
    (hU : IsOpen U) (h0U : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0 = 0) (hfd : HasFDerivAt f (ContinuousLinearMap.id ℝ E) 0)
    {b : ℝ} (hb : 0 < b) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ x, Φ 0 x = x) ∧ (fun x => Φ 1 x) =ᶠ[𝓝 0] f ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ ball 0 b ∧ ∀ t x, x ∉ C → Φ t x = x := by
  obtain ⟨h, hh, _, _, hnear⟩ := exists_compactField_extension
    (isCompact_singleton (x := (0 : E))) hU (singleton_subset_iff.mpr h0U)
    (fun x => f x - x) (hf.sub contDiff_id.contDiffOn)
  have hnear' : h =ᶠ[𝓝 (0 : E)] (fun x => f x - x) := by
    rw [nhdsSet_singleton] at hnear
    exact hnear
  have hh0 : h 0 = 0 := by simpa only [hf0, sub_self] using hnear'.eq_of_nhds
  have hhd : HasFDerivAt h (0 : E →L[ℝ] E) (0 : E) := by
    have hsub := hfd.fun_sub (hasFDerivAt_id (0 : E))
    simpa only [sub_self] using hsub.congr_of_eventuallyEq hnear'
  obtain ⟨g, hg, hgc, hgs, hglip, hgerm⟩ := exists_small_germ_extension h hh hh0
    hhd.fderiv (L := (1 / 2 : ℝ≥0)) (by norm_num) hb
  obtain ⟨Φ, hΦ, hformula, hzero, hone, _⟩ :=
    exists_smallPerturbation_isotopy g hg hgc (by norm_num) hglip
  refine ⟨Φ, hΦ, (fun x => hzero 0 x le_rfl), ?_, tsupport g, hgc, hgs, ?_⟩
  · filter_upwards [hgerm, hnear'] with x hgx hhx
    rw [hone 1 x le_rfl, hgx, hhx]
    abel
  · intro t x hx
    rw [hformula, image_eq_zero_of_notMem_tsupport hx, smul_zero, add_zero]

end PoincareConjecture.M25.Topology3D
