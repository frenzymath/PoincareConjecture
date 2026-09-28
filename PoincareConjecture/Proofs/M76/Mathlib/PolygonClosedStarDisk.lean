import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarBoundaryExtension
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLTriangleBoundary
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem isFinitePLBallPair_closedStar_of_polygon_link
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPlink : P.boundary ℝ = (K.link p).space) :
    IsFinitePLBallPair (ℝ × ℝ) (K.closedStar p).space (K.link p).space := by
  classical
  let a : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hap : a p = 0 := by change -p + p = 0; exact neg_add_cancel p
  let hf := K.affineOnFaces_affine a.toContinuousAffineMap
  let J := hf.embeddedImage a.injective.injOn
  have hJ : J.faces.Finite := hf.embeddedImage_finite a.injective.injOn hK
  have hJstar : (J.closedStar 0).space = a '' (K.closedStar p).space := by
    have h := hf.embeddedImage_closedStar_space a.injective.injOn hp
    change (J.closedStar (a p)).space = a '' (K.closedStar p).space at h
    simpa only [hap] using h
  have hJlink : (J.link 0).space = a '' (K.link p).space := by
    have h := hf.embeddedImage_link_space a.injective.injOn hp
    change (J.link (a p)).space = a '' (K.link p).space at h
    simpa only [hap] using h
  have hzJ : (0 : E) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices a.injective.injOn]
    exact ⟨p, hp, hap⟩
  have hne : (K.link p).space.Nonempty :=
    ⟨P 0, hPlink ▸ P.vertex_mem_boundary 0⟩
  have hneJ : (J.link 0).space.Nonempty := hJlink.symm ▸ hne.image a
  let T := Polygon.referenceTriangle 0
  have hT : AffineIndependent ℝ T := Polygon.affineIndependent_referenceTriangle 0
  let basis : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨T, hT,
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  let C := convexHull ℝ (range T)
  have hC : IsCompact C := (finite_range T).isCompact_convexHull ℝ
  have hcv : Convex ℝ C := convex_convexHull ℝ _
  obtain ⟨q, hq⟩ : (interior C).Nonempty := ⟨_, basis.centroid_mem_interior_convexHull⟩
  let b : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) := ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (-q)
  have hbq : b q = 0 := by change -q + q = 0; exact neg_add_cancel q
  have hbC : IsCompact (b '' C) := hC.image b.continuous
  have hbcv : Convex ℝ (b '' C) := hcv.affine_image b.toAffineEquiv.toAffineMap
  have hb0 : (0 : ℝ × ℝ) ∈ interior (b '' C) := by
    change (0 : ℝ × ℝ) ∈ interior (b.toHomeomorph '' C)
    rw [← b.toHomeomorph.image_interior]
    exact ⟨q, hq, hbq⟩
  have hfront : b '' frontier C = frontier (b '' C) := b.toHomeomorph.image_frontier C
  obtain ⟨e, he, _⟩ := P.exists_finitePL_triangle_boundary_model hP hinj T hT
  let e' := (Homeomorph.setCongr hPlink.symm).trans
    (e.trans (Homeomorph.setCongr (rfl : frontier C = frontier C)))
  have he' : e'.IsFinitePL := he.setCongr hPlink rfl
  let d := (a.toHomeomorph.image (K.link p).space).symm.trans
    (e'.trans (b.toHomeomorph.image (frontier C)))
  let d' := (Homeomorph.setCongr hJlink).trans (d.trans (Homeomorph.setCongr hfront))
  have hd' : d'.IsFinitePL := (he'.affine_conjugate a b).setCongr hJlink.symm hfront
  have hball := hd'.isFinitePLBallPair_closedStar J hJ hzJ hneJ hbC hbcv hb0
  have hback (S : Set E) : a.symm '' (a '' S) = S := by simp
  have himage := hball.affine_image a.symm.toContinuousAffineMap a.symm.injective.injOn
  change IsFinitePLBallPair (ℝ × ℝ)
    (a.symm '' (J.closedStar 0).space) (a.symm '' (J.link 0).space) at himage
  simpa only [hJstar, hJlink, hback] using himage

end Geometry.SimplicialComplex
