import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPreconnected.homothety_levels_subset_cut_side
    {D s₀ s₁ : Set E} (hD : IsPreconnected D) (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (A : E → ℝ) (hzero : s₀ ∩ s₁ ⊆ {x | A x = 0}) (q : E) (β : ℝ)
    (hcover : ∀ c ∈ Ioo (0 : ℝ) β, AffineMap.homothety q (c / β) '' D ⊆ s₀ ∪ s₁)
    (hlevel : ∀ c ∈ Ioo (0 : ℝ) β, ∀ x ∈ D, A (AffineMap.homothety q (c / β) x) = c) :
    (∀ c ∈ Ioo (0 : ℝ) β, AffineMap.homothety q (c / β) '' D ⊆ s₀ \ s₁) ∨
      (∀ c ∈ Ioo (0 : ℝ) β, AffineMap.homothety q (c / β) '' D ⊆ s₁ \ s₀) := by
  let f : ℝ × E → E := fun p => AffineMap.homothety q (p.1 / β) p.2
  have hf : Continuous f := by
    change Continuous (fun p : ℝ × E => (p.1 / β) • (p.2 - q) + q)
    exact ((continuous_fst.div_const β).smul (continuous_snd.sub continuous_const)).add
      continuous_const
  let S := f '' (Ioo (0 : ℝ) β ×ˢ D)
  have hS : IsPreconnected S := (isPreconnected_Ioo.prod hD).image f hf.continuousOn
  have hSc : S ⊆ s₀ ∪ s₁ := by
    rintro y ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩
    exact hcover c hc (mem_image_of_mem _ hx)
  have hSn : S ∩ (s₀ ∩ s₁) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩, hy⟩
    exact hc.1.ne' ((hlevel c hc x hx).symm.trans (hzero hy))
  have hslice (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) β) :
      AffineMap.homothety q (c / β) '' D ⊆ S := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨(c, x), ⟨hc, hx⟩, rfl⟩
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS s₀ s₁ hs₀ hs₁ hSc hSn with h | h
  · left
    intro c hc y hy
    have hyS := hslice c hc hy
    exact ⟨h hyS, fun hy₁ => (hSn.subset ⟨hyS, h hyS, hy₁⟩).elim⟩
  · right
    intro c hc y hy
    have hyS := hslice c hc hy
    exact ⟨h hyS, fun hy₀ => (hSn.subset ⟨hyS, hy₀, h hyS⟩).elim⟩

end Set

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]

theorem fixed_level_inter_image_cap (H : X ≃ₜ X) {R s d : Set X} {A : X → ℝ}
    (hfix : ∀ x ∈ R, H x = x) (hd : d ⊆ {x | A x = 0}) {c : ℝ} (hc : c ≠ 0) :
    (R ∩ {x | A x = c}) ∩ (H '' (s ∪ d)) = (R ∩ {x | A x = c}) ∩ s := by
  ext y
  constructor
  · rintro ⟨hy, x, hx, hxy⟩
    have hxy' : x = y := H.injective (hxy.trans (hfix y hy.1).symm)
    subst x
    rcases hx with hys | hyd
    · exact ⟨hy, hys⟩
    · exact (hc (hy.2.symm.trans (hd hyd))).elim
  · intro hy
    exact ⟨hy.1, y, Or.inl hy.2, hfix y hy.1.1⟩

end Homeomorph
