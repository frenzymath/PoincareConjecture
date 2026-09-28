import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.SourceDimension
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.AnnulusProjection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Rims" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

theorem source_rim_face_card_le (K : SimplicialComplex ℝ (V1 × V2))
    (hK : K.space = Rims) {a : Finset (V1 × V2)} (ha : a ∈ K.faces) :
    a.card ≤ 2 := by
  classical
  let J := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hJ := squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hJs : J.space = sphere (0 : V2) 1 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  have hJcard {b : Finset V2} (hb : b ∈ J.faces) : b.card ≤ 2 := by
    have hint : interior J.space = ∅ := by rw [hJs, interior_sphere']
    simpa only [Module.finrank_fin_fun] using
      J.face_card_le_of_interior_space_eq_empty hint hb
  have hJdim {b : Finset V2} (hb : b ∈ J.faces) :
      Module.finrank ℝ (affineSpan ℝ (b : Set V2)).direction ≤ 1 := by
    have hpos := Finset.card_pos.mpr (J.nonempty_of_mem_faces hb)
    have hcard : b.card = (b.card - 1) + 1 := by omega
    rw [J.finrank_faceDirection_of_card hb hcard]
    have hbound := hJcard hb
    omega
  let copy (b : Bool) : V2 →ᴬ[ℝ] (V1 × V2) :=
    (ContinuousAffineMap.const ℝ V2 (endpoint b)).prod (ContinuousAffineMap.id ℝ V2)
  let imageFace (b : Bool) (c : Finset V2) : AffineSubspace ℝ (V1 × V2) :=
    (affineSpan ℝ (c : Set V2)).map (copy b).toAffineMap
  let pool : Set (AffineSubspace ℝ (V1 × V2)) := ⋃ b : Bool, imageFace b '' J.faces
  have hpool : pool.Finite := Set.finite_iUnion fun b => hJ.image (imageFace b)
  let T := hpool.toFinset
  apply K.face_card_le_of_finite_affine_cover T (d := 1) ?_ ?_ ha
  · intro L hL
    obtain ⟨b, c, hc, rfl⟩ := mem_iUnion.mp (hpool.mem_toFinset.mp hL)
    change Module.finrank ℝ
      ((affineSpan ℝ (c : Set V2)).map (copy b).toAffineMap).direction ≤ 1
    rw [AffineSubspace.map_direction]
    exact (Submodule.finrank_map_le _ _).trans (hJdim hc)
  · intro x hx
    have hxrim := hK.subset hx
    obtain ⟨b, hb⟩ := (mem_sphere_iff_exists_endpoint x.1).mp hxrim.1
    obtain ⟨c, hc, hxc⟩ := J.mem_space_iff.mp (hJs.symm.subset hxrim.2)
    refine ⟨imageFace b c, hpool.mem_toFinset.mpr
      (mem_iUnion.mpr ⟨b, c, hc, rfl⟩), ?_⟩
    exact ⟨x.2, convexHull_subset_affineSpan (s := (c : Set V2)) hxc,
      Prod.ext hb.symm rfl⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
