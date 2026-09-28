import PoincareConjecture.Proofs.M14.Mathlib.WithinInverseSmooth
import PoincareConjecture.Proofs.M14.Mathlib.TimePreservingHomeomorph
import PoincareConjecture.Proofs.M14.Mathlib.ConvexLinearApproximation

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

set_option backward.isDefEq.respectTransparency false in

theorem exists_timePreserving_relative_inverse
    {f : E × ℝ → F × ℝ} {S : Set (E × ℝ)}
    (hSc : Convex ℝ S) (hS : UniqueDiffOn ℝ S) (hf : ContDiffOn ℝ ∞ f S)
    (hft : ∀ z ∈ S, (f z).2 = z.2) {x : E × ℝ} (hx : x ∈ S)
    (L : (E × ℝ) ≃L[ℝ] (F × ℝ))
    (hL : (L : (E × ℝ) →L[ℝ] (F × ℝ)) = fderivWithin ℝ f S x)
    (hLt : ∀ z, (L z).2 = z.2) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ x ∈ U ∧
      ∃ g : (E × ℝ) ≃ₜ (F × ℝ), EqOn f g (U ∩ S) ∧
        (∀ z, (g z).2 = z.2) ∧
        ContDiffOn ℝ ∞ g.symm (g '' (U ∩ S)) ∧
        ∀ z ∈ U ∩ S, (fderivWithin ℝ f S z).IsInvertible := by
  let : FiniteDimensional ℝ (E × ℝ) := L.symm.finiteDimensional
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_lt
    (inv_pos.mpr L.nnnorm_symm_pos) (lipschitzExtensionConstant F)
  obtain ⟨U₀, hU₀, hxU₀, happ⟩ :=
    exists_open_approximatesLinearOn hSc hS (hf.of_le (by simp)) hx c hcpos
  rw [← hL] at happ
  have hnear : ∀ᶠ z in 𝓝[S] x, (fderivWithin ℝ f S z).IsInvertible := by
    have hnhds := L.nhds
    rw [hL] at hnhds
    exact (hf.continuousOn_fderivWithin hS (by simp) x hx) hnhds
  obtain ⟨V, hV, hxV, hVinv⟩ := mem_nhdsWithin.mp hnear
  let U := U₀ ∩ V
  have hU : IsOpen U := hU₀.inter hV
  have hUS : U ∩ S ⊆ U₀ ∩ S := fun _ hz => ⟨hz.1.1, hz.2⟩
  obtain ⟨g, hgf, hgt⟩ := exists_timePreserving_homeomorph_extension
    (happ.mono_set hUS) (fun z hz => hft z hz.2) hLt hc
  have hinv (z : E × ℝ) (hz : z ∈ U ∩ S) :
      (fderivWithin ℝ f S z).IsInvertible := hVinv ⟨hz.1.2, hz.2⟩
  refine ⟨U, hU, ⟨hxU₀, hxV⟩, g, hgf, hgt, ?_, hinv⟩
  have hUSdiff : UniqueDiffOn ℝ (U ∩ S) := by
    rw [inter_comm]
    exact hS.inter hU
  apply contDiffOn_inverse_of_leftInverse hUSdiff (hf.mono inter_subset_right)
    g.symm.continuous.continuousOn
  · rintro y ⟨z, hz, rfl⟩
    simpa only [g.symm_apply_apply] using hz
  · rintro y ⟨z, hz, rfl⟩
    simpa only [g.symm_apply_apply] using hgf hz
  · intro z hz
    rw [inter_comm, fderivWithin_inter (hU.mem_nhds hz.1)]
    exact hinv z hz

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in

theorem timePreserving_image_inter (g : (E × ℝ) ≃ₜ (F × ℝ))
    (hgt : ∀ z, (g z).2 = z.2) (U : Set (E × ℝ)) (C : Set ℝ) :
    g '' (U ∩ (Prod.snd ⁻¹' C)) = g '' U ∩ (Prod.snd ⁻¹' C) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzU, hzC⟩, rfl⟩
    exact ⟨⟨z, hzU, rfl⟩, by simpa only [mem_preimage, hgt z] using hzC⟩
  · rintro ⟨⟨z, hzU, rfl⟩, hzC⟩
    exact ⟨z, ⟨hzU, by simpa only [mem_preimage, hgt z] using hzC⟩, rfl⟩

end PoincareConjecture.M14
