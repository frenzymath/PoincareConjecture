import PoincareLib.Topology.Manifold.Smoothing.Dehn.Barycentric.Mathlib.BarycentricOpenStars
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.OriginalFaceLabels
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.FiniteBarycentricCoordinates

/-!
# Actual geometric open stars retain every containing face

The inverse of the original finite barycentric homeomorphism defines
the open stars. Its exact support on every original face forces a
positive vertex coordinate to be a vertex of that same entire face.
This supplies the pair approximation in Hatcher, Theorem 3.1, p. 45,
reconstructed in Dehn derivations 022 section 3 and 023 sections 1--2.
-/

set_option autoImplicit false

open Set StdSimplexCore

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) [Fintype K.vertices]

/-- The actual positive-coordinate star in the original geometric
carrier and its original subspace topology. See Dehn 023, section 1. -/
def geometricOpenVertexStar (i : K.vertices) : Set K.space :=
  K.finiteBarycentricHomeomorph.symm ⁻¹'
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.openVertexStar i

/-- Each actual geometric positive-coordinate star is relatively open.
See Dehn derivation 023, section 1. -/
theorem isOpen_geometricOpenVertexStar (i : K.vertices) :
    IsOpen (K.geometricOpenVertexStar i) :=
  (K.vertexAbstractComplex.toPreAbstractSimplicialComplex.isOpen_openVertexStar i).preimage
    K.finiteBarycentricHomeomorph.symm.continuous

/-- The actual geometric stars cover the whole original carrier,
including all points on proper faces. See Dehn 023, section 1. -/
theorem exists_mem_geometricOpenVertexStar (x : K.space) :
    ∃ i, x ∈ K.geometricOpenVertexStar i :=
  K.vertexAbstractComplex.toPreAbstractSimplicialComplex.exists_mem_openVertexStar
    (K.finiteBarycentricHomeomorph.symm x)

/-- A positive coordinate belongs to every original face containing
the point. The exact inverse barycentric support proves this without
global affine independence. See Dehn derivation 023, section 1. -/
theorem mem_face_of_mem_geometricOpenVertexStar {x : K.space} {t : Finset E}
    (ht : t ∈ K.faces) (hxt : x.val ∈ convexHull ℝ (t : Set E))
    {i : K.vertices} (hi : x ∈ K.geometricOpenVertexStar i) : i.val ∈ t := by
  classical
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let s := K.allVertexFacesEquiv.symm ⟨t, ht⟩
  have hmap : s.val.map (Function.Embedding.subtype _) = t :=
    congrArg (fun q : K.faces => q.val) (K.allVertexFacesEquiv.apply_symm_apply ⟨t, ht⟩)
  have hset : (s.val.map (Function.Embedding.subtype _) : Set E) =
      Subtype.val '' (s.val : Set K.vertices) :=
    Finset.coe_map (Function.Embedding.subtype _) s.val
  have hx : x.val ∈ barycentricMap ((↑) : K.vertices → E) '' barycentricFace s.val := by
    rw [image_barycentricFace, ← hset, hmap]
    exact hxt
  obtain ⟨q, hq, hqx⟩ := hx
  let r : A.barycentricSpace := ⟨q, A.barycentricFace_subset_barycentricSpace s.property hq⟩
  have hrx : K.finiteBarycentricHomeomorph r = x := Subtype.ext hqx
  have hcoords : K.finiteBarycentricHomeomorph.symm x = r := by
    rw [← hrx, Homeomorph.symm_apply_apply]
  have hpos : 0 < (K.finiteBarycentricHomeomorph.symm x).val i := hi
  rw [hcoords] at hpos
  have his : i ∈ s.val :=
    A.mem_face_of_mem_openVertexStar (q := r) hq hpos
  rw [← hmap]
  exact Finset.mem_map.mpr ⟨i, his, rfl⟩

end Geometry.SimplicialComplex
