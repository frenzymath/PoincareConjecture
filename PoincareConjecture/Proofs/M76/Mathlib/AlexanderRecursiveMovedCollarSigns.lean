import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveResidualSigns
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabLevelCoverage
import PoincareConjecture.Proofs.M76.Mathlib.RaisingCutHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.VariableBandHeightSigns











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem AlexanderCollarSlab.mem_both_height_closures_of_capped_moved_collar
    {S s s' d B : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {x | A x = 0})
    (H : E ≃ₜ E) (hraise : ∀ x ∈ s, A x ≤ A (H x))
    (hneg : ∀ x ∈ s, A x < 0 → H x = x)
    (hfix : ∀ x ∈ M.residual, H x = x)
    {lower upper : E → ℝ}
    (D : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ≃ₜ
      (H '' (M.collar ∩ s)))
    (hDA : ∀ p, A (D p) = (p : E × ℝ).2)
    (hroof : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)},
      (p : E × ℝ).2 = upper (p : E × ℝ).1 → (D p : E) ∈ M.residual ∩ s)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)},
      (p : E × ℝ).2 = lower (p : E × ℝ).1 → 0 < A (D p) → (D p : E) ∈ H '' d)
    (hsource : ∀ x ∈ S, A x ∈ Ioo (0 : ℝ) β →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y}))
    (hcap : ∀ x ∈ H '' d, A x ∈ Ioo (0 : ℝ) β →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) :
    ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (0 : ℝ) β →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have htarget : H '' (M.collar ∩ s) ⊆ H '' (s ∪ d) :=
    image_mono (inter_subset_right.trans subset_union_left)
  have hcollar (x : E) (hx : x ∈ H '' (M.collar ∩ s))
      (hxA : A x ∈ Ioo (0 : ℝ) β) :
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
    let p := D.symm ⟨x, hx⟩
    have hp : (D p : E) = x := congrArg Subtype.val (D.apply_symm_apply _)
    have hfiber := D.mem_height_closures_of_variableBand A hDA p
    by_cases hlo : lower (p : E × ℝ).1 < (p : E × ℝ).2
    · have hlower := closure_mono (inter_subset_inter_left _ htarget) (hfiber.1 hlo)
      rw [hp] at hlower
      refine ⟨hlower, ?_⟩
      by_cases hhi : (p : E × ℝ).2 < upper (p : E × ℝ).1
      · have hupper := closure_mono (inter_subset_inter_left _ htarget) (hfiber.2 hhi)
        rwa [hp] at hupper
      · have htop : (p : E × ℝ).2 = upper (p : E × ℝ).1 :=
          le_antisymm p.property.2.2 (le_of_not_gt hhi)
        have hxR : x ∈ M.residual ∩ s := hp ▸ hroof p htop
        exact H.mem_upper_height_closure_of_raising_cut A hs' hunion hcut hraise
          hxR.2 hxA.1 (hfix x hxR.1) (hsource x (hsS hxR.2) hxA).2
    · have hbot : (p : E × ℝ).2 = lower (p : E × ℝ).1 :=
        le_antisymm (le_of_not_gt hlo) p.property.2.1
      have hxD : x ∈ H '' d := hp ▸ hbottom p hbot (hp.symm ▸ hxA.1)
      exact hcap x hxD hxA
  intro x hx hxA
  have hxcover := (image_capped_slab_level_eq hsS M.cover H hraise hneg hfix
    ⟨hxA.1, hxA.2.le⟩).subset ⟨hx, rfl⟩
  rcases hxcover.1 with hxT | hxR
  · obtain ⟨y, hyd | hyT, hyx⟩ := hxT
    · exact hcap x ⟨y, hyd, hyx⟩ hxA
    · exact hcollar x ⟨y, hyT, hyx⟩ hxA
  · by_cases hxT : x ∈ H '' (M.collar ∩ s)
    · exact hcollar x hxT hxA
    · have hxnot : x ∉ M.collar :=
        fun hxC => hxT ⟨x, ⟨hxC, hxR.2⟩, hfix x hxR.1⟩
      obtain ⟨hlo, hhi⟩ := hsource x (hsS hxR.2) hxA
      exact M.fixed_residual_mem_both_height_closures hs' hunion hcut H hfix
        hxR hxnot hxA hlo hhi

end Geometry
