import PoincareConjecture.Proofs.M76.Mathlib.InteriorConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem AffineOnFaces.isConnected_faceLink_of_embeddedImage [DecidableEq E]
    {K : SimplicialComplex ℝ V} {f : V → E} (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) {s : Finset V} (hs : s ∈ K.faces)
    (hconn : IsConnected ((hf.embeddedImage hinj).faceLink (s.image f)).space) :
    IsConnected (K.faceLink s).space := by
  rw [(hf.embeddedImage_faceLink_carrier_vertices hinj hs).1] at hconn
  have hfL : (K.faceLink s).AffineOnFaces f := fun t ht => hf t ht.1
  have hinjL : InjOn f (K.faceLink s).space :=
    hinj.mono (space_subset_of_le (fun _ ht => ht.1))
  exact isConnected_iff_connectedSpace.mpr
    ((hfL.homeomorphImage (finite_faceLink_faces hK s) hinjL).connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp hconn))

variable [FiniteDimensional ℝ E]





theorem isConnected_faceLink_of_faceAffine_vertex_stars
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hstars : ∀ p : V, {p} ∈ K.faces → ∃ a : V → E,
      (K.closedFaceStar {p}).AffineOnFaces a ∧
      InjOn a (K.closedFaceStar {p}).space ∧
      a p ∈ interior (a '' (K.closedFaceStar {p}).space)) :
    ∀ s ∈ K.faces, s.card < Module.finrank ℝ E → IsConnected (K.faceLink s).space := by
  classical
  intro s hs hscard
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨p, hps⟩
  have hp : {p} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  obtain ⟨a, hf, hinj, hint⟩ := hstars p hp
  let S := K.closedFaceStar {p}
  have hS : S.faces.Finite := finite_closedFaceStar_faces hK {p}
  have hsS : s ∈ S.faces := ⟨hs, by simpa [Finset.singleton_union, hps] using hs⟩
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hS
  have hsJ : s.image a ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  have hintJ : a p ∈ interior J.space := by
    rw [hf.embeddedImage_space hinj]
    exact hint
  have hcardJ : (s.image a).card = s.card :=
    Finset.card_image_iff.mpr (hinj.mono (S.subset_space hsS))
  have hdim : Module.finrank ℝ (affineSpan ℝ ((s.image a : Finset E) : Set E)).direction =
      s.card - 1 := J.finrank_faceDirection_of_card hsJ (by omega)
  have hcodim : Module.finrank ℝ (affineSpan ℝ ((s.image a : Finset E) : Set E)).direction + 1 <
      Module.finrank ℝ E := by rw [hdim]; omega
  have hlink := J.isConnected_faceLink_of_hull_meets_interior hJ hsJ hcodim
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  have hsource := hf.isConnected_faceLink_of_embeddedImage hinj hS hsS hlink
  exact (K.closedFaceStar_faceLink_of_subset
    (Finset.singleton_subset_iff.mpr hps)) ▸ hsource




theorem isConnected_faceLink_of_affine_vertex_stars
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hstars : ∀ p : V, {p} ∈ K.faces → ∃ a : V →ᴬ[ℝ] E,
      InjOn a (K.closedFaceStar {p}).space ∧
      a p ∈ interior (a '' (K.closedFaceStar {p}).space)) :
    ∀ s ∈ K.faces, s.card < Module.finrank ℝ E → IsConnected (K.faceLink s).space := by
  apply K.isConnected_faceLink_of_faceAffine_vertex_stars hK
  intro p hp
  obtain ⟨a, hinj, hint⟩ := hstars p hp
  exact ⟨a, (K.closedFaceStar {p}).affineOnFaces_affine a, hinj, hint⟩

end Geometry.SimplicialComplex
