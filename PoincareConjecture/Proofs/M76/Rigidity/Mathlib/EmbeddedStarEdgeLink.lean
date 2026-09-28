import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.InteriorEdgeLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_polygon_faceLink_of_embedded_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (h3 : Module.finrank ℝ F = 3) {s : Finset E}
    (hs : s ∈ K.faces) (hscard : s.card = 2) {p : E} (hps : p ∈ s)
    (f : E → F) (hf : (K.closedStar p).AffineOnFaces f)
    (hi : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space)) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (K.faceLink s).space := by
  classical
  let N := K.closedStar p
  have hsN : s ∈ N.faces :=
    ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  let J := hf.embeddedImage hi
  have hJ : J.faces.Finite := hf.embeddedImage_finite hi
    (hK.subset (fun _ ht => ht.1))
  have hsJ : s.image f ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hi (N.subset_space hsN)).mpr hsN
  have hcardJ : (s.image f).card = 2 :=
    (Finset.card_image_iff.mpr (hi.mono (N.subset_space hsN))).trans hscard
  have hintJ : f p ∈ interior J.space := by
    rw [hf.embeddedImage_space hi]
    exact hint
  obtain ⟨n, P, hPi, hP, hPs⟩ := J.exists_polygon_faceLink_of_interior_edge
    hJ h3 hsJ hcardJ
    ⟨f p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  let q := Function.invFunOn f N.space
  have hq : FinitePiecewiseAffineOn q J.space :=
    (hf.invFunOn_embeddedImage hi).finitePiecewiseAffineOn hJ
  have hqi : InjOn q J.space := by
    change InjOn (Function.invFunOn f N.space) J.space
    rw [hf.embeddedImage_space hi]
    exact Function.invFunOn_injOn_image f N.space
  have hPsub : P.boundary ℝ ⊆ J.space := by
    rw [hPs]
    exact space_subset_of_le (show J.faceLink (s.image f) ≤ J from fun _ ht => ht.1)
  obtain ⟨m, Q, hQi, hQ, hQb⟩ := P.exists_polygon_finitePL_image
    hP hPi hq hPsub (hqi.mono hPsub)
  have hlinkN : (N.faceLink s).space ⊆ N.space :=
    space_subset_of_le (show N.faceLink s ≤ N from fun _ ht => ht.1)
  have hNl : N.faceLink s = K.faceLink s := by
    change (K.closedStar p).faceLink s = K.faceLink s
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  refine ⟨m, Q, hQi, hQ, ?_⟩
  rw [hQb, hPs, (hf.embeddedImage_faceLink_carrier_vertices hi hsN).1]
  change Function.invFunOn f N.space '' (f '' (N.faceLink s).space) = _
  rw [hi.invFunOn_image hlinkN, hNl]

end Geometry.SimplicialComplex
