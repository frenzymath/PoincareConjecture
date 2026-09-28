import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryDerivedLevelSets
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]





theorem image_barycentricNeighborhood_binaryCenters
    (A : SimplicialComplex ℝ E) {F : E → E} {h : E → ℝ}
    (hF : K.barycentricSubdivision.AffineOnFaces F)
    (hcenters : ∀ s : K.faces, F (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices)
    (hh : K.AffineOnFaces h)
    (hvalues : ∀ v ∈ K.vertices,
      (v ∈ A.vertices → h v = 1) ∧ (v ∉ A.vertices → h v = 0)) :
    F '' (K.barycentricNeighborhood A).space =
      K.space ∩ {x | (1 / 2 : ℝ) ≤ h x} := by
  classical
  let c : K.faces → E := fun s => s.val.centroid ℝ id
  let d : K.faces → E := fun s => s.val.binaryFaceCenter A.vertices
  let D := K.derivedSubdivision d (K.positive_binary_face_centers A.vertices)
  let N := D.vertexSubcomplex {x | (1 / 2 : ℝ) ≤ h x}
  have hfaceValues (s : K.faces) (v : E) (hv : v ∈ s.val) :
      (v ∈ A.vertices → h v = 1) ∧ (v ∉ A.vertices → h v = 0) :=
    hvalues v (K.down_closed s.property (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))
  have hchainImage (a : Finset K.faces) (ha : a.Nonempty)
      (hchain : ∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) :
      F '' convexHull ℝ (a.image c : Set E) = convexHull ℝ (a.image d : Set E) := by
    have hface : a.image c ∈ K.barycentricSubdivision.faces :=
      (K.barycentricSubdivision_faces _).mpr ⟨a, ha, hchain, rfl⟩
    have himage : F '' (a.image c : Set E) = (a.image d : Set E) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_image.mpr ⟨s, hs, (hcenters s).symm⟩
      · intro hx
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨c s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, hcenters s⟩
    rw [hF.image_convexHull hface, himage]
  have hN : N.space = K.space ∩ {x | (1 / 2 : ℝ) ≤ h x} :=
    hh.binaryDerived_superlevel_space A.vertices hvalues
  rw [← hN]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
    obtain ⟨a, ha, hchain, rfl⟩ := (K.barycentricSubdivision_faces t).mp ht.1
    have hlabels (s : K.faces) (hs : s ∈ a) : ∃ v ∈ s.val, v ∈ A.vertices := by
      obtain ⟨u, hu, huA, huc⟩ := ht.2 (c s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
      have hus : (⟨u, hu⟩ : K.faces) = s := K.faceCentroid_injective huc
      have hval : u = s.val := congrArg Subtype.val hus
      simpa only [hval] using huA
    have hretained : a.image d ∈ N.faces := by
      refine ⟨(K.derivedSubdivision_faces d (K.positive_binary_face_centers A.vertices) _).mpr
        ⟨a, ha, hchain, rfl⟩, ?_⟩
      intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      exact (hh.half_le_binaryFaceCenter_iff s.property A.vertices (hfaceValues s)).mpr
        (hlabels s hs)
    exact N.convexHull_subset_space hretained
      ((hchainImage a ha hchain).subset ⟨y, hyt, rfl⟩)
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha, hchain, rfl⟩ :=
      (K.derivedSubdivision_faces d (K.positive_binary_face_centers A.vertices) t).mp ht.1
    have hlabels (s : K.faces) (hs : s ∈ a) : ∃ v ∈ s.val, v ∈ A.vertices := by
      apply (hh.half_le_binaryFaceCenter_iff s.property A.vertices (hfaceValues s)).mp
      exact ht.2 (d s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    have hretained : a.image c ∈ (K.barycentricNeighborhood A).faces := by
      refine ⟨(K.barycentricSubdivision_faces _).mpr ⟨a, ha, hchain, rfl⟩, ?_⟩
      intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨s.val, s.property, hlabels s hs, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (hchainImage a ha hchain).superset hxt
    exact ⟨y, (K.barycentricNeighborhood A).convexHull_subset_space hretained hy, hyx⟩

end Geometry.SimplicialComplex
