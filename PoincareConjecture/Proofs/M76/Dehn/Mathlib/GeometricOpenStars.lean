import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BarycentricOpenStars
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalFaceLabels
import PoincareConjecture.Proofs.M76.Mathlib.FiniteBarycentricCoordinates











set_option autoImplicit false

open Set StdSimplexCore

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) [Fintype K.vertices]



def geometricOpenVertexStar (i : K.vertices) : Set K.space :=
  K.finiteBarycentricHomeomorph.symm ⁻¹'
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.openVertexStar i



theorem isOpen_geometricOpenVertexStar (i : K.vertices) :
    IsOpen (K.geometricOpenVertexStar i) :=
  (K.vertexAbstractComplex.toPreAbstractSimplicialComplex.isOpen_openVertexStar i).preimage
    K.finiteBarycentricHomeomorph.symm.continuous



theorem exists_mem_geometricOpenVertexStar (x : K.space) :
    ∃ i, x ∈ K.geometricOpenVertexStar i :=
  K.vertexAbstractComplex.toPreAbstractSimplicialComplex.exists_mem_openVertexStar
    (K.finiteBarycentricHomeomorph.symm x)




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
