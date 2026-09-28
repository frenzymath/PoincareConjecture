import PoincareConjecture.Proofs.M76.Mathlib.ConvexProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_proper_arc_cut
    {s q U V W : Set E} {a b : E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hU : IsFinitePLBallPair ℝ U {a, b})
    (hV : IsFinitePLBallPair ℝ V {a, b})
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hUV : U ∩ V ⊆ {a, b}) (hrim : U ∪ V = q)
    (hproper : W \ {a, b} ⊆ s \ q) :
    ∃ d₀ d₁ : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d₀ (U ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁ (W ∪ V) ∧
      d₀ ∪ d₁ = s ∧ d₀ ∩ d₁ = W ∧ d₀ ∩ q = U ∧ d₁ ∩ q = V := by
  obtain ⟨hqs, C, hC, hcv, hne, e, he, heb⟩ := hs
  have hUs : U ⊆ s := (subset_union_left.trans hrim.subset).trans hqs
  have hVs : V ⊆ s := (subset_union_right.trans hrim.subset).trans hqs
  have habs : ({a, b} : Set E) ⊆ s := hU.1.trans hUs
  have hWs : W ⊆ s := by
    intro x hx
    by_cases hm : x ∈ ({a, b} : Set E)
    · exact habs hm
    · exact (hproper ⟨hx, hm⟩).1
  have has : a ∈ s := habs (by simp)
  have hbs : b ∈ s := habs (by simp)
  have hecopy := he
  obtain ⟨f, hf, heval⟩ := hecopy
  obtain ⟨g, hg, hgval⟩ := he.symm
  have hgf : LeftInvOn g f s := by
    intro x hx
    rw [← heval ⟨x, hx⟩, ← hgval, e.symm_apply_apply]
  have hfg : LeftInvOn f g C := by
    intro y hy
    rw [← hgval ⟨y, hy⟩, ← heval, e.apply_symm_apply]
  have hfmap (x : E) (hx : x ∈ s) : f x ∈ C := by
    rw [← heval ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hgmap (y : ℝ × ℝ) (hy : y ∈ C) : g y ∈ s := by
    rw [← hgval ⟨y, hy⟩]
    exact (e.symm ⟨y, hy⟩).property
  have hbound (x : E) (hx : x ∈ s) : x ∈ q ↔ f x ∈ frontier C := by
    simpa only [heval] using heb ⟨x, hx⟩
  have hfbound : f '' q = frontier C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hbound x (hqs hx)).mp hx
    · intro hy
      have hyC := hC.isClosed.frontier_subset hy
      refine ⟨g y, (hbound _ (hgmap y hyC)).mpr ?_, hfg hyC⟩
      rwa [hfg hyC]
  have hgfimage {t : Set E} (ht : t ⊆ s) : g '' (f '' t) = t := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      rw [hgf (ht hy)] at hyx
      exact hyx ▸ hy
    · intro hx
      exact ⟨f x, mem_image_of_mem f hx, hgf (ht hx)⟩
  have hgC : g '' C = s := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hgmap y hy
    · intro x hx
      exact ⟨f x, hfmap x hx, hgf hx⟩
  have hgbound : g '' frontier C = q := by
    rw [← hfbound]
    exact hgfimage hqs
  have hUi : IsFinitePLBallPair ℝ (f '' U) {f a, f b} := by
    simpa only [image_pair] using hU.image_of_subset hf hUs hgf.injOn
  have hVi : IsFinitePLBallPair ℝ (f '' V) {f a, f b} := by
    simpa only [image_pair] using hV.image_of_subset hf hVs hgf.injOn
  have hWi : IsFinitePLBallPair ℝ (f '' W) {f a, f b} := by
    simpa only [image_pair] using hW.image_of_subset hf hWs hgf.injOn
  have habi : f a ≠ f b := fun h => hab (hgf.injOn has hbs h)
  have hUVi : (f '' U) ∩ (f '' V) ⊆ {f a, f b} := by
    rw [← hgf.injOn.image_inter hUs hVs, ← image_pair]
    exact image_mono hUV
  have hrimi : (f '' U) ∪ (f '' V) = frontier C := by
    rw [← image_union, hrim, hfbound]
  have hproperi : (f '' W) \ {f a, f b} ⊆ interior C := by
    rintro _ ⟨⟨x, hx, rfl⟩, hnot⟩
    have hxnot : x ∉ ({a, b} : Set E) := by
      intro hx'
      apply hnot
      rw [← image_pair]
      exact mem_image_of_mem f hx'
    have hxproper := hproper ⟨hx, hxnot⟩
    by_contra hni
    exact hxproper.2 ((hbound x hxproper.1).mpr
      ⟨subset_closure (hfmap x hxproper.1), hni⟩)
  obtain ⟨D₀, D₁, hD₀, hD₁, hwhole, hcommon, houter₀, houter₁⟩ :=
    hC.exists_finitePL_disk_cut_of_proper_arc hcv hne hUi hVi hWi habi hUVi hrimi hproperi
  have hD₀C : D₀ ⊆ C := subset_union_left.trans hwhole.subset
  have hD₁C : D₁ ⊆ C := subset_union_right.trans hwhole.subset
  have hd₀ := hD₀.image_of_subset hg hD₀C hfg.injOn
  have hd₁ := hD₁.image_of_subset hg hD₁C hfg.injOn
  rw [image_union, hgfimage hUs, hgfimage hWs] at hd₀
  rw [image_union, hgfimage hWs, hgfimage hVs] at hd₁
  refine ⟨g '' D₀, g '' D₁, hd₀, hd₁, ?_, ?_, ?_, ?_⟩
  · rw [← image_union, hwhole, hgC]
  · rw [← hfg.injOn.image_inter hD₀C hD₁C, hcommon, hgfimage hWs]
  · rw [← hgbound, ← hfg.injOn.image_inter hD₀C hC.isClosed.frontier_subset,
      houter₀, hgfimage hUs]
  · rw [← hgbound, ← hfg.injOn.image_inter hD₁C hC.isClosed.frontier_subset,
      houter₁, hgfimage hVs]

end Set
