import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryNeighborhoodModel
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ConeHeightLink
import PoincareConjecture.Proofs.M76.Mathlib.AffineSubdivisionComposition
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualEdgeDisk












set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

set_option maxHeartbeats 1000000 in

omit [Fintype K.faces] in




theorem subcomplex_preserving_pullback_affineOnFaces
    (R : SimplicialComplex ℝ E) (hRK : R.IsSubdivision K) {F : E → E} {h : E → ℝ}
    (hF : R.AffineOnFaces F) (hh : K.AffineOnFaces h)
    (hmarks : ∀ L : SimplicialComplex ℝ E, L ≤ K → F '' L.space = L.space) :
    R.AffineOnFaces (h ∘ F) := by
  classical
  apply hF.comp_of_hull_images hh
  intro s hs
  obtain ⟨t, ht, hst⟩ := hRK.face_subset s hs
  let L := K.finiteFaceSpan {⟨t, ht⟩}
  have hL : L.space = convexHull ℝ (t : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hxu⟩ := mem_space_iff.mp hx
      obtain ⟨_, v, hv, huv⟩ := (K.finiteFaceSpan_faces {⟨t, ht⟩} u).mp hu
      have hvt : v = ⟨t, ht⟩ := Finset.mem_singleton.mp hv
      subst v
      exact convexHull_mono huv hxu
    · intro hx
      apply L.convexHull_subset_space (s := t) _ hx
      exact (K.finiteFaceSpan_faces {⟨t, ht⟩} t).mpr
        ⟨K.nonempty_of_mem_faces ht, ⟨t, ht⟩, Finset.mem_singleton_self _, Subset.rfl⟩
  have himage := hmarks L (K.finiteFaceSpan_le {⟨t, ht⟩})
  rw [hL] at himage
  exact ⟨t, ht, fun x hx => himage.subset ⟨x, hst hx, rfl⟩⟩

variable [DecidableEq E]






theorem image_dualBlock_link_binaryLevel
    (A : SimplicialComplex ℝ E) (hAK : A ≤ K)
    (hfull : ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ A.vertices) → t ∈ A.faces)
    {F : E → E} {h : E → ℝ}
    (hF : K.barycentricSubdivision.AffineOnFaces F) (hh : K.AffineOnFaces h)
    (hcenters : ∀ t : K.faces, F (t.val.centroid ℝ id) = t.val.binaryFaceCenter A.vertices)
    (hvalues : ∀ v ∈ K.vertices,
      (v ∈ A.vertices → h v = 1) ∧ (v ∉ A.vertices → h v = 0))
    (hmarks : ∀ L : SimplicialComplex ℝ E, L ≤ K → F '' L.space = L.space)
    {s : Finset E} (hsA : s ∈ A.faces)
    (hmax : ∀ t ∈ A.faces, s ⊆ t → t = s) :
    F '' ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space =
        (F '' (K.barycentricDualBlock s).space) ∩ {x | h x = (1 / 2 : ℝ)} ∧
      F '' ((K.barycentricDualBlock s).space \
          ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space) =
        (F '' (K.barycentricDualBlock s).space) ∩ {x | (1 / 2 : ℝ) < h x} := by
  classical
  let N := K.barycentricDualBlock s
  let c := s.centroid ℝ id
  let k := h ∘ F
  have hsK : s ∈ K.faces := hAK hsA
  have hk : N.AffineOnFaces k :=
    fun t ht => K.subcomplex_preserving_pullback_affineOnFaces
      K.barycentricSubdivision K.barycentricSubdivision_isSubdivision hF hh hmarks t ht.1
  have hapex : k c = 1 := by
    change h (F (s.centroid ℝ id)) = 1
    rw [hcenters ⟨s, hsK⟩]
    apply hh.binaryFaceCenter_const hsK A.vertices 1
    intro v hv
    exact (hvalues v (K.face_subset_vertices hsK hv)).1 (A.face_subset_vertices hsA hv)
  have hother (v : E) (hv : v ∈ N.vertices) (hvc : v ≠ c) : k v = (1 / 2 : ℝ) := by
    obtain ⟨t, ht, hst, htv⟩ := hv.2 v (Finset.mem_singleton_self v)
    have hts : t ≠ s := by
      intro he
      subst t
      exact hvc htv.symm
    have hselected : ∃ z ∈ t, z ∈ A.vertices := by
      obtain ⟨z, hz⟩ := A.nonempty_of_mem_faces hsA
      exact ⟨z, hst hz, A.face_subset_vertices hsA hz⟩
    have hunselected : ∃ z ∈ t, z ∉ A.vertices := by
      by_contra hn
      push Not at hn
      exact hts (hmax t (hfull t ht hn) hst)
    rw [← htv]
    change h (F (t.centroid ℝ id)) = (1 / 2 : ℝ)
    rw [hcenters ⟨t, ht⟩]
    apply hh.binaryFaceCenter_mixed ht A.vertices
    · exact ⟨Finset.filter_nonempty_iff.mpr hselected,
        Finset.filter_nonempty_iff.mpr hunselected⟩
    · intro z hz
      exact hvalues z (K.face_subset_vertices ht hz)
  obtain ⟨hlower, hlink⟩ := hk.closedStar_link_level c (1 / 2 : ℝ)
    (K.barycentricDualBlock_closedStar_faceCentroid hsK) (by rw [hapex]; norm_num) hother
  constructor
  · change F '' (N.link c).space = (F '' N.space) ∩ {x | h x = (1 / 2 : ℝ)}
    rw [hlink]
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hlevel⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hlevel⟩
    · rintro ⟨⟨x, hx, rfl⟩, hlevel⟩
      exact ⟨x, ⟨hx, hlevel⟩, rfl⟩
  · change F '' (N.space \ (N.link c).space) =
      (F '' N.space) ∩ {x | (1 / 2 : ℝ) < h x}
    rw [hlink]
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxnot⟩, rfl⟩
      have hne : k x ≠ (1 / 2 : ℝ) := fun he => hxnot ⟨hx, he⟩
      exact ⟨⟨x, hx, rfl⟩, lt_of_le_of_ne (hlower x hx) hne.symm⟩
    · rintro ⟨⟨x, hx, rfl⟩, hhigh⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      rintro ⟨_, he⟩
      exact hhigh.ne' he

end Geometry.SimplicialComplex
