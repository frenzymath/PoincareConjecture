import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Real.Basic

/-!
# Geometric images under simplex-preserving maps

A map need not be affine to carry a complex to another geometric
complex. Exact hull images, independent image vertices and carrier
injectivity suffice. This covers the projective simplex maps in
Hamilton 1976, pp. 67--68; see Hudson 1969, pp. 15--19 and
M76 derivation 86.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  (K : SimplicialComplex ℝ E) (f : E → F)
  (hinj : InjOn f K.space)
  (hind : ∀ s ∈ K.faces, AffineIndependent ℝ ((↑) : ↥(f '' (s : Set E)) → F))
  (hhull : ∀ s ∈ K.faces,
    f '' convexHull ℝ (s : Set E) = convexHull ℝ (f '' (s : Set E)))

/-- The geometric image of a carrier-injective map preserving
simplex hulls and independent vertices. See Hudson pp. 15--19
and M76 derivation 86. -/
noncomputable def hullImage : SimplicialComplex ℝ F := by
  classical
  refine { K.toPreAbstractSimplicialComplex.map f with
    indep := ?_
    inter_subset_convexHull := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    change AffineIndependent ℝ ((↑) : ↥((s.image f : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact hind s hs
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ y ⟨hys, hyt⟩
    simp only [Finset.coe_image] at hys hyt ⊢
    rw [← hhull s hs] at hys
    rw [← hhull t ht] at hyt
    obtain ⟨x, hx, hxy⟩ := hys
    obtain ⟨z, hz, hzy⟩ := hyt
    have he : x = z := hinj (K.convexHull_subset_space hs hx)
      (K.convexHull_subset_space ht hz) (hxy.trans hzy.symm)
    have hxi := K.inter_subset_convexHull hs ht ⟨hx, he.symm ▸ hz⟩
    have hsint : s ∩ t ∈ K.faces := K.down_closed hs Finset.inter_subset_left
      (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, by simpa using hxi⟩))
    have hyi : y ∈ convexHull ℝ (f '' ((s : Set E) ∩ t)) := by
      rw [← Finset.coe_inter, ← hhull (s ∩ t) hsint]
      exact ⟨x, by simpa using hxi, hxy⟩
    exact convexHull_mono (Set.image_inter_subset _ _ _) hyi

/-- Hull-image faces are precisely the finite images of original
faces. See Hudson pp. 15--19 and M76 derivation 86. -/
theorem hullImage_faces [DecidableEq F] :
    (K.hullImage f hinj hind hhull).faces =
      (fun s : Finset E => s.image f) '' K.faces := by
  classical
  change (fun s : Finset E => @Finset.image E F (Classical.decEq F) f s) '' K.faces = _
  congr 1
  funext s
  ext y
  simp only [Finset.mem_image]

/-- The hull-image carrier is exactly the image of the original
carrier. See Hudson pp. 15--19 and M76 derivation 86. -/
theorem hullImage_space : (K.hullImage f hinj hind hhull).space = f '' K.space := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
    rw [K.hullImage_faces f hinj hind hhull] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [Finset.coe_image, ← hhull s hs] at hyt
    obtain ⟨x, hx, hxy⟩ := hyt
    exact ⟨x, K.convexHull_subset_space hs hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    apply convexHull_subset_space (s := s.image f)
      (show s.image f ∈ (K.hullImage f hinj hind hhull).faces from
        (K.hullImage_faces f hinj hind hhull) ▸ mem_image_of_mem _ hs)
    rw [Finset.coe_image, ← hhull s hs]
    exact mem_image_of_mem f hxs

/-- Hull-image vertices are exactly the images of original
vertices. See Hudson pp. 15--19 and M76 derivation 86. -/
theorem hullImage_vertices : (K.hullImage f hinj hind hhull).vertices = f '' K.vertices := by
  classical
  ext y
  constructor
  · intro hy
    have hface : {y} ∈ (K.hullImage f hinj hind hhull).faces := hy
    rw [K.hullImage_faces f hinj hind hhull] at hface
    obtain ⟨s, hs, he⟩ := hface
    have hymem : y ∈ s.image f := by
      change s.image f = {y} at he
      rw [he]
      exact Finset.mem_singleton_self y
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hymem
    exact ⟨x, K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty x), hxy⟩
  · rintro ⟨x, hx, rfl⟩
    change {f x} ∈ (K.hullImage f hinj hind hhull).faces
    rw [K.hullImage_faces f hinj hind hhull]
    exact ⟨{x}, hx, by simp⟩

end Geometry.SimplicialComplex
