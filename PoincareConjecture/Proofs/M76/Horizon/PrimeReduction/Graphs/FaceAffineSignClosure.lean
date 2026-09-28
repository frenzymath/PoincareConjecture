import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_positive_face_of_mem_height_closure
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ)
    {p : E} (hp : p ∈ closure (K.space ∩ {x | 0 < A x})) :
    ∃ s ∈ K.faces, p ∈ convexHull ℝ (s : Set E) ∧ ∃ v ∈ s, 0 < A v := by
  let T : Set (Finset E) := {s | s ∈ K.faces ∧ ∃ v ∈ s, 0 < A v}
  have hT : T.Finite := hK.subset (fun _ hs => hs.1)
  have hclosed : IsClosed (⋃ s ∈ T, convexHull ℝ (s : Set E)) :=
    hT.isClosed_biUnion (fun s _ => (s.finite_toSet.isCompact_convexHull ℝ).isClosed)
  have hsub : K.space ∩ {x | 0 < A x} ⊆ ⋃ s ∈ T, convexHull ℝ (s : Set E) := by
    rintro x ⟨hxK, hxA⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxK
    have hpos : ∃ v ∈ s, 0 < A v := by
      by_contra! h
      have hle : convexHull ℝ (s : Set E) ⊆ {y | A y ≤ 0} :=
        convexHull_min (fun v hv => h v hv) ((convex_Iic (0 : ℝ)).affine_preimage A)
      exact (not_lt_of_ge (show A x ≤ 0 from hle hxs)) (show 0 < A x from hxA)
    exact mem_iUnion₂.mpr ⟨s, ⟨hs, hpos⟩, hxs⟩
  obtain ⟨s, hsT, hps⟩ := mem_iUnion₂.mp (closure_minimal hsub hclosed hp)
  exact ⟨s, hsT.1, hps, hsT.2⟩

theorem AffineOnFaces.mem_positive_height_closure_image
    {K : SimplicialComplex ℝ E} {f : E → F} (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ)
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B (f v))
    {p : E} (hp : p ∈ closure (K.space ∩ {x | 0 < A x}))
    (hzero : B (f p) = 0) :
    f p ∈ closure ((f '' K.space) ∩ {y | 0 < B y}) := by
  obtain ⟨s, hs, hps, v, hv, hvA⟩ := K.exists_positive_face_of_mem_height_closure hK A hp
  have hfp : f p ∈ convexHull ℝ (f '' (s : Set E)) :=
    (hf.image_convexHull hs).subset (mem_image_of_mem f hps)
  have hfv : f v ∈ convexHull ℝ (f '' (s : Set E)) :=
    subset_convexHull ℝ _ (mem_image_of_mem f hv)
  have hvK : v ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hvB := hpos v hvK hvA
  have hnear := (convex_convexHull ℝ (f '' (s : Set E))).mem_closure_upper_affine_height
    B hfp hfv (by simpa only [hzero] using hvB)
  rw [hzero] at hnear
  apply closure_mono _ hnear
  rintro y ⟨hy, hyB⟩
  exact ⟨(image_mono (K.convexHull_subset_space hs)) ((hf.image_convexHull hs).symm.subset hy),
    hyB⟩

theorem AffineOnFaces.mem_negative_height_closure_image
    {K : SimplicialComplex ℝ E} {f : E → F} (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ)
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B (f v) < 0)
    {p : E} (hp : p ∈ closure (K.space ∩ {x | A x < 0}))
    (hzero : B (f p) = 0) :
    f p ∈ closure ((f '' K.space) ∩ {y | B y < 0}) := by
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
    hf.mem_positive_height_closure_image hK (-A) (-B)
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hneg)
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hp)
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hzero)

theorem AffineOnFaces.mem_both_height_closures_image
    {K : SimplicialComplex ℝ E} {f : E → F} (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) (B : F →ᵃ[ℝ] ℝ)
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < B (f v))
    (hneg : ∀ v ∈ K.vertices, A v < 0 → B (f v) < 0)
    {p : E} (hp : p ∈ closure (K.space ∩ {x | A x < 0}) ∧
      p ∈ closure (K.space ∩ {x | 0 < A x}))
    (hzero : B (f p) = 0) :
    f p ∈ closure ((f '' K.space) ∩ {y | B y < 0}) ∧
      f p ∈ closure ((f '' K.space) ∩ {y | 0 < B y}) :=
  ⟨hf.mem_negative_height_closure_image hK A B hneg hp.1 hzero,
    hf.mem_positive_height_closure_image hK A B hpos hp.2 hzero⟩

end Geometry.SimplicialComplex
