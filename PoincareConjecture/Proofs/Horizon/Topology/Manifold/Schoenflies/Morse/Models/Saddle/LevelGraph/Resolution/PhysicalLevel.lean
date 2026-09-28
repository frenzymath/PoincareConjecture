import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Hyperbola

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
variable {X : Type*} [TopologicalSpace X]

theorem strip_slice_subset_source
    (F : OpenPartialHomeomorph (Real × Real) X) {a b w t : Real}
    (hFs : F.source = Ioo (a - w) (b + w) ×ˢ Ioo (-w) w)
    (hw : 0 < w) (ht : t ∈ Ioo (-w) w) :
    Icc a b ×ˢ ({t} : Set Real) ⊆ F.source := by
  rw [hFs]
  intro z hz
  have hzt : z.2 = t := hz.2
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hzt ▸ ht⟩

theorem isCompact_strip_slice
    (F : OpenPartialHomeomorph (Real × Real) X) {a b w t : Real}
    (hFs : F.source = Ioo (a - w) (b + w) ×ˢ Ioo (-w) w)
    (hw : 0 < w) (ht : t ∈ Ioo (-w) w) :
    IsCompact (F '' (Icc a b ×ˢ ({t} : Set Real))) := by
  apply (isCompact_Icc.prod isCompact_singleton).image_of_continuousOn
  exact F.continuousOn.mono (strip_slice_subset_source F hFs hw ht)

theorem isPreconnected_strip_slice
    (F : OpenPartialHomeomorph (Real × Real) X) {a b w t : Real}
    (hFs : F.source = Ioo (a - w) (b + w) ×ˢ Ioo (-w) w)
    (hw : 0 < w) (ht : t ∈ Ioo (-w) w) :
    IsPreconnected (F '' (Icc a b ×ˢ ({t} : Set Real))) := by
  apply (isPreconnected_Icc.prod isPreconnected_singleton).image
  exact F.continuousOn.mono (strip_slice_subset_source F hFs hw ht)

theorem fiber_eq_square_slice_union_strip_slices
    {h : X → Real} {c : Real}
    (e : OpenPartialHomeomorph E2 X)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    {r w η : Real} (hw : 0 < w) (hηw : η < w)
    (hrs : closedSquare r ⊆ e.source)
    {a b : Fin 2 → Real}
    {F : Fin 2 → OpenPartialHomeomorph (Real × Real) X}
    (hFs : ∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w)
    (hFheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hband : h ⁻¹' Icc (c - η) (c + η) ⊆
      e '' openSquare r ∪ ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η))
    {t : Real} (ht : t ∈ Icc (-η) η) :
    h ⁻¹' {c + t} =
      e '' (closedSquare r ∩ {x : E2 | -(x 0) ^ 2 + x 1 ^ 2 = t}) ∪
        ⋃ i, F i '' (Icc (a i) (b i) ×ˢ ({t} : Set Real)) := by
  have hsource (i : Fin 2) : Icc (a i) (b i) ×ˢ Icc (-η) η ⊆ (F i).source := by
    intro z hz
    rw [hFs i]
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  apply Subset.antisymm
  · intro q hq
    change h q = c + t at hq
    have hqband : q ∈ h ⁻¹' Icc (c - η) (c + η) := by
      change h q ∈ Icc (c - η) (c + η)
      rw [hq]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rcases hband hqband with hpatch | hstrips
    · left
      obtain ⟨x, hx, rfl⟩ := hpatch
      have hxe : x ∈ e.source := hrs (openSquare_subset_closedSquare r hx)
      refine ⟨x, ⟨openSquare_subset_closedSquare r hx, ?_⟩, rfl⟩
      rw [hform x hxe] at hq
      change -(x 0) ^ 2 + x 1 ^ 2 = t
      linarith
    · right
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hstrips
      have hzval : z.2 = t := by
        linarith [hFheight i z (hsource i hz)]
      exact mem_iUnion_of_mem i ⟨z, ⟨hz.1, hzval⟩, rfl⟩
  · rintro q (hq | hq)
    · obtain ⟨x, ⟨hx, hlevel⟩, rfl⟩ := hq
      change h (e x) = c + t
      rw [hform x (hrs hx)]
      change -(x 0) ^ 2 + x 1 ^ 2 = t at hlevel
      linarith
    · obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hq
      have hzt : z.2 = t := hz.2
      change h (F i z) = c + t
      rw [hFheight i z (hsource i ⟨hz.1, hzt ▸ ht⟩), hzt]

theorem positive_physical_level_eq_resolution
    {h : X → Real} {c : Real}
    (e : OpenPartialHomeomorph E2 X)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    {r w η : Real} (hr : 0 < r) (hηw : η < w) (hrs : closedSquare r ⊆ e.source)
    {a b : Fin 2 → Real}
    {F : Fin 2 → OpenPartialHomeomorph (Real × Real) X}
    (hFs : ∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w)
    (hFheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hband : h ⁻¹' Icc (c - η) (c + η) ⊆
      e '' openSquare r ∪ ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η))
    {t : Real} (ht : 0 < t) (hte : t < η) (htr : t < r ^ 2) :
    h ⁻¹' {c + t} =
      (⋃ i : Fin 2, e '' (positiveLevelArc t i ''
        Icc (-hyperbolaRadius r t) (hyperbolaRadius r t))) ∪
        ⋃ i, F i '' (Icc (a i) (b i) ×ˢ ({t} : Set Real)) := by
  rw [fiber_eq_square_slice_union_strip_slices e hform (by linarith) hηw hrs
    hFs hFheight hband ⟨by linarith, by linarith⟩]
  rw [closedSquare_positiveLevel_eq_arcs hr ht htr, image_iUnion]

theorem negative_physical_level_eq_resolution
    {h : X → Real} {c : Real}
    (e : OpenPartialHomeomorph E2 X)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    {r w η : Real} (hr : 0 < r) (hηw : η < w) (hrs : closedSquare r ⊆ e.source)
    {a b : Fin 2 → Real}
    {F : Fin 2 → OpenPartialHomeomorph (Real × Real) X}
    (hFs : ∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w)
    (hFheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hband : h ⁻¹' Icc (c - η) (c + η) ⊆
      e '' openSquare r ∪ ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η))
    {t : Real} (ht : 0 < t) (hte : t < η) (htr : t < r ^ 2) :
    h ⁻¹' {c - t} =
      (⋃ i : Fin 2, e '' (negativeLevelArc t i ''
        Icc (-hyperbolaRadius r t) (hyperbolaRadius r t))) ∪
        ⋃ i, F i '' (Icc (a i) (b i) ×ˢ ({-t} : Set Real)) := by
  rw [sub_eq_add_neg c t,
    fiber_eq_square_slice_union_strip_slices e hform (by linarith) hηw hrs
      hFs hFheight hband ⟨by linarith, by linarith⟩]
  rw [closedSquare_negativeLevel_eq_arcs hr ht htr, image_iUnion]

end Poincare.Manifold.Schoenflies.SaddleLevel
