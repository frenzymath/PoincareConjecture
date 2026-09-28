import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnSide
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanCorner

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_jordan_nested_of_frontier_subset
    {U₁ V₁ U₂ V₂ : Set AnnulusCoordinates}
    (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
    (hpV₁ : IsPreconnected V₁) (hbU₂ : Bornology.IsBounded U₂)
    (hbV₁ : ¬ Bornology.IsBounded V₁)
    (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
    (hc₁ : U₁ ∪ V₁ = (frontier U₁)ᶜ)
    (hc₂ : U₂ ∪ V₂ = (frontier U₂)ᶜ)
    (hf₁ : frontier U₁ = frontier V₁)
    (hsub : frontier U₂ ⊆ closure U₁) : U₂ ⊆ U₁ := by
  have hdcl : Disjoint (closure U₁) V₁ := hd₁.closure_left hV₁
  have hVcover : V₁ ⊆ U₂ ∪ V₂ := by
    rw [hc₂]
    exact fun x hx hf => disjoint_left.mp hdcl (hsub hf) hx
  have hVV : V₁ ⊆ V₂ := by
    rcases hpV₁.subset_or_subset hU₂ hV₂ hd₂ hVcover with h | h
    · exact False.elim (hbV₁ (hbU₂.subset h))
    · exact h
  have hUcl : U₂ ⊆ closure U₁ := by
    intro x hx
    by_contra hn
    have hxf : x ∉ frontier U₁ := fun hf => hn (frontier_subset_closure hf)
    have hxcover : x ∈ U₁ ∪ V₁ := by rwa [hc₁]
    rcases hxcover with hx₁ | hx₁
    · exact hn (subset_closure hx₁)
    · exact disjoint_left.mp hd₂ hx (hVV hx₁)
  calc
    U₂ = interior U₂ := hU₂.interior_eq.symm
    _ ⊆ interior (closure U₁) := interior_mono hUcl
    _ = U₁ := (m64Intrinsic_jordan_interior_closure hU₁ hV₁ hd₁ hf₁).1

theorem m64Intrinsic_one_of_two_regions_is_annular
    {U₁ V₁ U₂ V₂ : Set AnnulusCoordinates}
    (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
    (hpV₁ : IsPreconnected V₁) (hbU₂ : Bornology.IsBounded U₂)
    (hbV₁ : ¬ Bornology.IsBounded V₁)
    (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
    (hc₁ : U₁ ∪ V₁ = (frontier U₁)ᶜ)
    (hc₂ : U₂ ∪ V₂ = (frontier U₂)ᶜ)
    (hf₁ : frontier U₁ = frontier V₁)
    (hcompact₁ : IsCompact (closure U₁)) (hcompact₂ : IsCompact (closure U₂))
    (htrace₁ : frontier U₁ ⊆ standardAnnulusDomain)
    (htrace₂ : frontier U₂ ⊆ standardAnnulusDomain)
    (hshared : frontier U₂ ⊆ frontier U₁ ∪ closedBall (0 : AnnulusCoordinates) 1)
    {p : AnnulusCoordinates} (hp : ‖p‖ = 1)
    (hp₁ : p ∈ frontier U₁) (hp₂ : p ∉ frontier U₂) :
    closure U₁ ⊆ standardAnnulusDomain ∨ closure U₂ ⊆ standardAnnulusDomain := by
  rcases m64Intrinsic_jordan_annulus_dichotomy hU₁ hV₁ hd₁ hc₁ rfl hcompact₁
      htrace₁ with h | hball
  · exact Or.inl h
  right
  have hclosedBall : closedBall (0 : AnnulusCoordinates) 1 ⊆ closure U₁ := by
    rw [← closure_ball (0 : AnnulusCoordinates) (by norm_num : (1 : ℝ) ≠ 0)]
    exact closure_mono hball
  have hfrontsub : frontier U₂ ⊆ closure U₁ :=
    hshared.trans (union_subset frontier_subset_closure hclosedBall)
  have hUU := m64Intrinsic_jordan_nested_of_frontier_subset hU₁ hV₁ hU₂ hV₂
    hpV₁ hbU₂ hbV₁ hd₁ hd₂ hc₁ hc₂ hf₁ hfrontsub
  have hpnot : p ∉ U₁ := by simpa only [hU₁.interior_eq] using hp₁.2
  have hpV₂ : p ∈ V₂ := by
    have hpc : p ∈ U₂ ∪ V₂ := by rwa [hc₂]
    exact hpc.resolve_left (fun h => hpnot (hUU h))
  have hpball : p ∈ closure (ball (0 : AnnulusCoordinates) 1) := by
    rw [closure_ball (0 : AnnulusCoordinates) (by norm_num : (1 : ℝ) ≠ 0)]
    simp only [mem_closedBall, dist_zero_right, hp, le_refl]
  obtain ⟨x, hxV₂, hxball⟩ := mem_closure_iff.mp hpball V₂ hV₂ hpV₂
  have hballcover : ball (0 : AnnulusCoordinates) 1 ⊆ U₂ ∪ V₂ := by
    rw [hc₂]
    intro z hz hf
    have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    exact not_lt_of_ge (htrace₂ hf).1 hz'
  have hballV₂ : ball (0 : AnnulusCoordinates) 1 ⊆ V₂ := by
    rcases (convex_ball (0 : AnnulusCoordinates) (1 : ℝ)).isPreconnected.subset_or_subset
        hU₂ hV₂ hd₂ hballcover with h | h
    · exact False.elim (disjoint_left.mp hd₂ (h hxball) hxV₂)
    · exact h
  apply m64Intrinsic_jordan_closure_subset_annulus hcompact₂ ?_ htrace₂
  exact fun hzero => disjoint_left.mp (hd₂.closure_left hV₂) hzero
    (hballV₂ (mem_ball_self zero_lt_one))

end PoincareConjecture
