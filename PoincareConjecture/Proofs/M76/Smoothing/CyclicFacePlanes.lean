import PoincareConjecture.Proofs.M76.Mathlib.RadialConeLabels
import PoincareConjecture.Proofs.M76.Mathlib.CofaceFrames
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarPlaneCoordinates
import PoincareConjecture.Proofs.M76.Smoothing.TangentCycleProjections
import Mathlib.LinearAlgebra.Complex.FiniteDimensional











set_option autoImplicit false

open Set Geometry ContinuousLinearMap AbstractSimplicialComplex

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]






theorem contractible_cyclicFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {n : ℕ}
    (e : Fin (n + 3) ≃ (K.faceLink s).vertices)
    (hfaces : ∀ t : Finset (Fin (n + 3)),
      t ∈ (cyclicEdgeComplex n).faces ↔
        t.map e.toEmbedding ∈ (K.faceLink s).vertexAbstractComplex.faces) :
    ContractibleSpace (SecantTransversePlaneSpace
      (2 + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction)
      (K.closedFaceStar s).space) := by
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ affineSpan ℝ (s : Set E) := mem_affineSpan ℝ hps
  let L := (affineSpan ℝ (s : Set E)).direction
  let f := L.normalAffineProjection p
  let v := K.faceNormalRadialEmbedding hK hs hp
  have hw : LinearIndependent ℝ (fun i => f (e i)) :=
    (K.linearIndependent_faceLink_normal hK hs hp).comp e e.injective
  let w : (cyclicEdgeComplex n).RadialEmbedding ↥(Lᗮ) :=
    ⟨fun i => f (e i), (cyclicEdgeComplex n).isRadialEmbedding_of_linearIndependent hw⟩
  let V := Submodule.span ℝ (range w.val)
  let b : Module.Basis (Fin (n + 3)) ℝ V := Module.Basis.span hw
  let J := V.subtypeL.comp (cycleFrameInclusion b)
  have hJ : Function.Injective J :=
    fun x y h => injective_cycleFrameInclusion b (Subtype.val_injective h)
  have hnormal : f '' (K.closedFaceStar s).space =
      V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space := by
    rw [K.normal_image_closedFaceStar hK hs hp]
    have hcone : w.cone = v.cone := v.cone_eq_of_reindex w e hfaces (fun _ => rfl)
    rw [w.subtype_basis_span_cone_space hw, hcone]
  let : ContractibleSpace (FrameEmbeddingSpace J (f '' (K.closedFaceStar s).space)) := by
    rw [hnormal]
    exact contractible_ambientCycleFrameEmbeddingSpace n V b
  let t : Finset E := {(e 0 : E), (e 1 : E)}
  have htlink : t ∈ (K.faceLink s).faces := by
    have h := (hfaces {0, 1}).mp
      (show ({0, 1} : Finset (Fin (n + 3))) ∈ (cyclicEdgeComplex n).faces from
        ⟨Finset.insert_nonempty _ _, 0, by simp⟩)
    change (({0, 1} : Finset (Fin (n + 3))).map e.toEmbedding).map
      (Function.Embedding.subtype _) ∈ (K.faceLink s).faces at h
    simpa only [Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype, Equiv.coe_toEmbedding] using h
  have ht : s ∪ t ∈ (K.closedFaceStar s).faces :=
    ⟨htlink.2.2, by simpa only [← Finset.union_assoc, Finset.union_self] using htlink.2.2⟩
  let U := affineSpan ℝ ((s ∪ t : Finset E) : Set E)
  have hsub : affineSpan ℝ (s : Set E) ≤ U :=
    affineSpan_mono ℝ (show (s : Set E) ⊆ ((s ∪ t : Finset E) : Set E) from
      Finset.subset_union_left)
  have hvertices : ∀ i ∈ ({0, 1} : Finset (Fin (n + 3))), (f (e i) : E) ∈ U.direction := by
    intro i hi
    apply AffineSubspace.normalAffineProjection_mem_direction _ U hsub hp
    apply mem_affineSpan ℝ
    apply Finset.mem_union_right s
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hb : ∀ i, (V.subtype (b i) : ↥(Lᗮ)) = f (e i) :=
    fun i => Module.Basis.coe_span_apply hw i
  have hframe : (L.frameWithTangent J).range ≤ U.direction := by
    apply L.frameWithTangent_range_le U.direction J (AffineSubspace.direction_le hsub)
    intro z
    change ((V.subtype (z.re • b 0 + z.im • b 1) : ↥(Lᗮ)) : E) ∈ U.direction
    rw [map_add, map_smul, map_smul, hb, hb]
    exact U.direction.add_mem (U.direction.smul_mem z.re (hvertices 0 (by simp)))
      (U.direction.smul_mem z.im (hvertices 1 (by simp)))
  have h := K.contractible_faceStarTransversePlaneSpace hK hs hp J hJ ht hframe
  rwa [Complex.finrank_real_complex] at h

end PoincareConjecture.M76.Smoothing
