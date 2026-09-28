import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem compact_collar_cut_geometry
    {X : Type*} [TopologicalSpace X] [T2Space X] {R U : Set X}
    (hR : IsCompact R) (hU : IsOpen U) (hUR : closure U ⊆ interior R) :
    IsCompact (R \ U) ∧
      interior (R \ U) = interior R \ closure U ∧
      frontier (R \ U) = frontier R ∪ frontier U ∧
      closure U ∩ (R \ U) = frontier U ∧
      closure U ∪ (R \ U) = R ∧
      Disjoint (frontier R) (frontier U) := by
  have hclosed : IsClosed (R \ U) := hR.isClosed.inter hU.isClosed_compl
  have hUC : U ⊆ closure U := subset_closure
  have hCR : closure U ⊆ R := hUR.trans interior_subset
  have hint : interior (R \ U) = interior R \ closure U := by
    rw [sdiff_eq, interior_inter, interior_compl]
    rfl
  have hfrontU : frontier U = closure U \ U := by
    rw [frontier, hU.interior_eq]
  refine ⟨hR.of_isClosed_subset hclosed sdiff_subset, hint, ?_, ?_, ?_, ?_⟩
  · rw [frontier, hclosed.closure_eq, hint, hfrontU]
    ext x
    constructor
    · rintro ⟨⟨hxR, hxU⟩, hxint⟩
      by_cases hi : x ∈ interior R
      · exact Or.inr ⟨by
          by_contra hc
          exact hxint ⟨hi, hc⟩, hxU⟩
      · exact Or.inl ⟨subset_closure hxR, hi⟩
    · rintro (hx | hx)
      · refine ⟨⟨hR.isClosed.frontier_subset hx, ?_⟩, fun hi => hx.2 hi.1⟩
        intro hu
        exact hx.2 (hUR (hUC hu))
      · exact ⟨⟨hCR hx.1, hx.2⟩, fun hi => hi.2 hx.1⟩
  · rw [hfrontU]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hCR hx.1, hx.2⟩⟩
  · apply Subset.antisymm (union_subset hCR sdiff_subset)
    intro x hx
    by_cases hu : x ∈ U
    · exact Or.inl (hUC hu)
    · exact Or.inr ⟨hx, hu⟩
  · apply disjoint_left.mpr
    intro x hxR hxU
    exact hxR.2 (hUR (frontier_subset_closure hxU))

theorem exists_collar_level_homeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {A : Set E} (hA : IsCompact A) (c : E × ℝ → X)
    (hc : Topology.IsEmbedding
      (fun z : (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    ∃ H : A ≃ₜ c '' (A ×ˢ ({r} : Set ℝ)),
      (∀ x : A, (H x : X) = c ((x : E), r)) ∧
      IsCompact (c '' (A ×ˢ ({r} : Set ℝ))) := by
  let f : A → X := fun x => c ((x : E), r)
  have hf : Continuous f := hc.continuous.comp
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk
      (fun x => ⟨x.property, hr⟩))
  have hfi : Function.Injective f := by
    intro x y hxy
    have he : (⟨((x : E), r), ⟨x.property, hr⟩⟩ :
        (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ))) = ⟨((y : E), r), ⟨y.property, hr⟩⟩ := hc.injective
      (show c (⟨((x : E), r), ⟨x.property, hr⟩⟩ :
        (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ))) =
        c (⟨((y : E), r), ⟨y.property, hr⟩⟩ :
          (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ))) from hxy)
    exact Subtype.ext (congrArg Prod.fst (congrArg Subtype.val he))
  have hrange : range f = c '' (A ×ˢ ({r} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨((x : E), r), ⟨x.property, rfl⟩, rfl⟩
    · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
      have hur : u = r := hu
      subst u
      exact ⟨⟨x, hx⟩, rfl⟩
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let H := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)
  refine ⟨H, fun _ => rfl, ?_⟩
  rw [← hrange]
  exact isCompact_range hf

theorem disjoint_collar_level_images
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : Set E} (c : E × ℝ → X)
    (hc : Topology.IsEmbedding
      (fun z : (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {r q : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1)
    (hrq : r ≠ q) :
    Disjoint (c '' (A ×ˢ ({r} : Set ℝ))) (c '' (A ×ˢ ({q} : Set ℝ))) := by
  apply disjoint_left.mpr
  rintro _ ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩ ⟨⟨y, v⟩, ⟨hy, hv⟩, he⟩
  have hur : u = r := hu
  have hvq : v = q := hv
  subst u
  subst v
  have hpair : (⟨(y, q), ⟨hy, hq⟩⟩ : (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ))) =
      ⟨(x, r), ⟨hx, hr⟩⟩ := hc.injective
    (show c (⟨(y, q), ⟨hy, hq⟩⟩ : (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ))) =
      c (⟨(x, r), ⟨hx, hr⟩⟩ : (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ))) from he)
  exact hrq (congrArg Prod.snd (congrArg Subtype.val hpair)).symm

end PoincareConjecture.M76
