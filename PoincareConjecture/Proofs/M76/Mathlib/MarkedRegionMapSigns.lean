import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateFourRegionIncidence

set_option autoImplicit false

open Set CoordinateFourRegions

namespace Homeomorph

theorem mem_marked_subsets_of_extension
    {E F ι : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {S g : Set E} {T h : Set F} (H : S ≃ₜ T) (G : g ≃ₜ h)
    (hgs : g ⊆ S) (hht : h ⊆ T)
    (hkeep : ∀ x : g, H ⟨x, hgs x.property⟩ = ⟨G x, hht (G x).property⟩)
    (A : ι → Set E) (B : ι → Set F)
    (hAg : ∀ i, A i ⊆ g) (hBh : ∀ i, B i ⊆ h)
    (hmem : ∀ i (x : g), (x : E) ∈ A i ↔ (G x : F) ∈ B i) :
    ∀ i (x : S), (x : E) ∈ A i ↔ (H x : F) ∈ B i := by
  have hgraph := H.mem_subset_iff_of_extension G hgs hht hkeep
  have hval (x : g) : (H ⟨x, hgs x.property⟩ : F) = G x :=
    congrArg Subtype.val (hkeep x)
  intro i x
  constructor
  · intro hx
    have hxg := hAg i hx
    have hy := (hmem i ⟨x, hxg⟩).mp hx
    rwa [← hval] at hy
  · intro hy
    have hxg := (hgraph x).mpr (hBh i hy)
    apply (hmem i ⟨x, hxg⟩).mpr
    rwa [← hval]

theorem coordinate_signs_of_marked_regions
    {E : Type*} [TopologicalSpace E] {F P : Set E}
    {T : Set ((ℝ × ℝ) × ℝ)} (H : F ≃ₜ T)
    (disk sourceArc : Bool × Bool → Set E) (A : E → ℝ)
    (hheight : ∀ i : Bool,
      disk (i, false) ∪ disk (i, true) = F ∩ {x | weakSign i (A x)})
    (hlink : sourceArc (true, false) ∪ sourceArc (true, true) = P)
    (hregions : ∀ i (x : F), (x : E) ∈ disk i ↔ (H x : (ℝ × ℝ) × ℝ) ∈ region T i)
    (harcs : ∀ i (x : F), (x : E) ∈ sourceArc i ↔ (H x : (ℝ × ℝ) × ℝ) ∈ arc T i) :
    (∀ x : F, 0 ≤ A x ↔ 0 ≤ (H x : (ℝ × ℝ) × ℝ).1.1) ∧
      (∀ x : F, A x ≤ 0 ↔ (H x : (ℝ × ℝ) × ℝ).1.1 ≤ 0) ∧
      ∀ x : F, (x : E) ∈ P ↔ (H x : (ℝ × ℝ) × ℝ).2 = 0 := by
  have hsign (i : Bool) (x : F) :
      weakSign i (A x) ↔ weakSign i (H x : (ℝ × ℝ) × ℝ).1.1 := by
    have hm : (x : E) ∈ disk (i, false) ∪ disk (i, true) ↔
        (H x : (ℝ × ℝ) × ℝ) ∈ region T (i, false) ∪ region T (i, true) :=
      or_congr (hregions (i, false) x) (hregions (i, true) x)
    rw [hheight i, region_height_union] at hm
    exact ⟨fun hx => (hm.mp ⟨x.property, hx⟩).2,
      fun hx => (hm.mpr ⟨(H x).property, hx⟩).2⟩
  refine ⟨hsign false, hsign true, ?_⟩
  intro x
  have hm : (x : E) ∈ sourceArc (true, false) ∪ sourceArc (true, true) ↔
      (H x : (ℝ × ℝ) × ℝ) ∈ arc T (true, false) ∪ arc T (true, true) :=
    or_congr (harcs (true, false) x) (harcs (true, true) x)
  rw [hlink, arc_kind_union] at hm
  exact ⟨fun hx => (hm.mp hx).2, fun hx => hm.mpr ⟨(H x).property, hx⟩⟩

end Homeomorph
