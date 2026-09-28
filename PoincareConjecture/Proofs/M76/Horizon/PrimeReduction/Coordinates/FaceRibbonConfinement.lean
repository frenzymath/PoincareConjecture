import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PlanePairSignTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AffineTriangleComponents









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem mapsTo_returning_strand_face_interiors
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (ℝ × ℝ) →ᴬ[ℝ] V) (R : V →ᴬ[ℝ] (ℝ × ℝ))
    (hRF : Function.LeftInverse R F)
    {triangle base : Set V}
    (hFR : EqOn (F ∘ R) id triangle)
    (hbase : F '' (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) = base)
    (f : (ℝ × ℝ) → ℝ × ℝ) (c : ℝ)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, f (c, t) ∈ interior (R '' triangle))
    (hends : ∀ t ∈ ({0, 1} : Set ℝ),
      (f (c, t)).1 ∈ Ioo (0 : ℝ) 1 ∧ (f (c, t)).2 = 0) :
    MapsTo F ((fun t : ℝ => f (c, t)) '' Icc (0 : ℝ) 1)
      (intrinsicInterior ℝ triangle ∪ intrinsicInterior ℝ base) := by
  have htriangle : F '' (R '' triangle) = triangle := by
    rw [image_image]
    exact EqOn.image_eq_self hFR
  have hFi := hRF.injective
  rintro _ ⟨t, ht, rfl⟩
  by_cases hEnd : t ∈ ({0, 1} : Set ℝ)
  · right
    have hh := hends t hEnd
    rw [← hbase]
    change F (f (c, t)) ∈ intrinsicInterior ℝ (F.toAffineMap '' _)
    rw [F.toAffineMap.intrinsicInterior_image_of_injOn_span _ hFi.injOn]
    refine mem_image_of_mem F ?_
    rw [intrinsicInterior_prod_eq, intrinsicInterior_singleton]
    exact ⟨interior_subset_intrinsicInterior (by simpa only [interior_Icc] using hh.1), hh.2⟩
  · left
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hEnd
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hEnd.1), lt_of_le_of_ne ht.2 hEnd.2⟩
    rw [← htriangle]
    change F (f (c, t)) ∈ intrinsicInterior ℝ (F.toAffineMap '' _)
    rw [F.toAffineMap.intrinsicInterior_image_of_injOn_span _ hFi.injOn]
    exact mem_image_of_mem F (interior_subset_intrinsicInterior (hinterior t ht'))




theorem mapsTo_returning_strand_original_face_interiors
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (K : Geometry.SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s a : Finset E} (hs : s ∈ K.faces) (has : a ⊆ s)
    (Q : OpenPartialHomeomorph X (Fin 3 → ℝ)) (A : E →ᴬ[ℝ] (Fin 3 → ℝ))
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (F : (ℝ × ℝ) →ᴬ[ℝ] (Fin 3 → ℝ)) (R : (Fin 3 → ℝ) →ᴬ[ℝ] (ℝ × ℝ))
    (hRF : Function.LeftInverse R F)
    (hFR : EqOn (F ∘ R) id (convexHull ℝ (A '' (s : Set E))))
    (hbase : F '' (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) =
      convexHull ℝ (A '' (a : Set E)))
    (f : (ℝ × ℝ) → ℝ × ℝ) (c : ℝ)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1,
      f (c, t) ∈ interior (R '' convexHull ℝ (A '' (s : Set E))))
    (hends : ∀ t ∈ ({0, 1} : Set ℝ),
      (f (c, t)).1 ∈ Ioo (0 : ℝ) 1 ∧ (f (c, t)).2 = 0) :
    MapsTo F ((fun t : ℝ => f (c, t)) '' Icc (0 : ℝ) 1)
      (A '' (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
        intrinsicInterior ℝ (convexHull ℝ (a : Set E)))) := by
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hAsp := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hAi
  have hAap := hAsp.mono (affineSpan_mono ℝ (convexHull_mono has))
  have htransport (b : Finset E)
      (hb : InjOn A (affineSpan ℝ (convexHull ℝ (b : Set E)))) :
      intrinsicInterior ℝ (convexHull ℝ (A '' (b : Set E))) =
        A '' intrinsicInterior ℝ (convexHull ℝ (b : Set E)) := by
    change intrinsicInterior ℝ (convexHull ℝ (A.toAffineMap '' (b : Set E))) =
      A.toAffineMap '' intrinsicInterior ℝ (convexHull ℝ (b : Set E))
    rw [← A.toAffineMap.image_convexHull]
    exact A.toAffineMap.intrinsicInterior_image_of_injOn_span _ hb
  have h := mapsTo_returning_strand_face_interiors F R hRF hFR hbase f c hinterior hends
  rw [htransport s hAsp, htransport a hAap, ← image_union] at h
  exact h

end PoincareConjecture.M76
