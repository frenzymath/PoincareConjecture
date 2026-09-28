import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.PhysicalLevel
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Levels

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem image_strip_slice_of_flattening {X : Type*}
    (g : X → E3) (D : E3 → E3) (v : E3) (F : Real × Real → X)
    {a b t : Real}
    (hflat : ∀ s ∈ Icc a b, D (g (F (s, t))) = g (F (s, 0)) + t • v) :
    (D ∘ g) '' (F '' (Icc a b ×ˢ ({t} : Set Real))) =
      (fun s => g (F (s, 0)) + t • v) '' Icc a b := by
  ext y
  constructor
  · rintro ⟨q, ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩, rfl⟩
    have hut : u = t := hu
    subst u
    exact ⟨s, hs, (hflat s hs).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨F (s, t), ⟨(s, t), ⟨hs, rfl⟩, rfl⟩, hflat s hs⟩

theorem flattened_fiber_eq_patch_union_strip_slices
    {X : Type*} [TopologicalSpace X] {h : X → Real} {c : Real}
    (g : X → E3) (D : E3 → E3) (v : E3)
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
    (hflat : ∀ i t, t ∈ Icc (-η) η → ∀ s ∈ Icc (a i) (b i),
      D (g (F i (s, t))) = g (F i (s, 0)) + t • v)
    {t : Real} (ht : t ∈ Icc (-η) η) :
    (D ∘ g) '' (h ⁻¹' {c + t}) =
      (D ∘ g ∘ e) '' (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ∪
      ⋃ i, (fun s => g (F i (s, 0)) + t • v) '' Icc (a i) (b i) := by
  rw [fiber_eq_square_slice_union_strip_slices e hform hw hηw hrs
    hFs hFheight hband ht, image_union, image_iUnion, ← image_comp]
  congr 1
  apply iUnion_congr
  intro i
  exact image_strip_slice_of_flattening g D v (F i) (hflat i t ht)

theorem flattened_exterior_eq_recut_strip_slices
    {X : Type*} [TopologicalSpace X] {h : X → Real} {c r η t : Real}
    (g : X → E3) (D : E3 → E3) (v : E3)
    (e : OpenPartialHomeomorph E2 X)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) X)
    (a b A B : Fin 2 → Real)
    (hA : ∀ i, a i ≤ A i) (hB : ∀ i, B i ≤ b i)
    (hexterior : (h ⁻¹' {c + t}) \ e '' openSquare r =
      ⋃ i, F i '' (Icc (A i) (B i) ×ˢ ({t} : Set Real)))
    (hflat : ∀ i t, t ∈ Icc (-η) η → ∀ s ∈ Icc (a i) (b i),
      D (g (F i (s, t))) = g (F i (s, 0)) + t • v)
    (ht : t ∈ Icc (-η) η) :
    (D ∘ g) '' ((h ⁻¹' {c + t}) \ e '' openSquare r) =
      ⋃ i, (fun s => g (F i (s, 0)) + t • v) '' Icc (A i) (B i) := by
  rw [hexterior, image_iUnion]
  apply iUnion_congr
  intro i
  apply image_strip_slice_of_flattening
  intro s hs
  exact hflat i t ht s ⟨(hA i).trans hs.1, hs.2.trans (hB i)⟩

end Poincare.Manifold.Schoenflies.Saddle.Levels
