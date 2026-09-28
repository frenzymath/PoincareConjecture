import PoincareConjecture.Proofs.M76.Smoothing.TwoPointNormalSpace
import PoincareConjecture.Proofs.M76.Mathlib.SmallFaceLinks
import PoincareConjecture.Proofs.M76.Mathlib.CofaceFrames
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarPlaneCoordinates











set_option autoImplicit false

open Set Geometry ContinuousLinearMap

namespace PoincareConjecture.M76.Smoothing

section Singleton

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F]




theorem contractible_singletonFrameEmbeddingSpace (J : F →L[ℝ] E) :
    ContractibleSpace (FrameEmbeddingSpace J ({0} : Set E)) := by
  have : Nonempty (FrameEmbeddingSpace J ({0} : Set E)) := by
    refine ⟨⟨0, (fun _ => Subsingleton.elim _ _), ?_⟩⟩
    intro x hx y hy _
    exact (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm
  infer_instance

end Singleton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem contractible_twoPointFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {u v : E} (huv : u ≠ v)
    (hlink : (K.faceLink s).faces = {({u} : Finset E), {v}}) :
    ContractibleSpace (SecantTransversePlaneSpace
      (1 + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction) (K.closedFaceStar s).space) := by
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ affineSpan ℝ (s : Set E) := mem_affineSpan ℝ hps
  let L := (affineSpan ℝ (s : Set E)).direction
  let f := L.normalAffineProjection p
  have hf : ∀ x ∈ s, f x = 0 := fun x hx =>
    L.normalAffineProjection_eq_zero p
      ((affineSpan ℝ (s : Set E)).vsub_mem_direction (mem_affineSpan ℝ hx) hp)
  have hu : u ∈ (K.faceLink s).vertices := by
    change {u} ∈ (K.faceLink s).faces
    rw [hlink]
    exact Or.inl rfl
  have hv : v ∈ (K.faceLink s).vertices := by
    change {v} ∈ (K.faceLink s).faces
    rw [hlink]
    exact Or.inr rfl
  let labels : Fin 2 → (K.faceLink s).vertices := ![⟨u, hu⟩, ⟨v, hv⟩]
  have hlabels : Function.Injective labels := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (huv (congrArg Subtype.val hij)).elim
    · exact (huv (congrArg Subtype.val hij).symm).elim
    · rfl
  have hpair : LinearIndependent ℝ ![f u, f v] := by
    convert (K.linearIndependent_faceLink_normal hK hs hp).comp labels hlabels using 1
    funext i
    fin_cases i <;> rfl
  let J : ℝ →L[ℝ] ↥(Lᗮ) := toSpanSingleton ℝ (f u)
  have hJ : Function.Injective J := smul_left_injective ℝ (hpair.ne_zero 0)
  have hnormal : f '' (K.closedFaceStar s).space = twoRayStar (f u) (f v) :=
    K.affine_image_closedFaceStar_twoPoint hs f hf hlink
  let : ContractibleSpace (FrameEmbeddingSpace J (f '' (K.closedFaceStar s).space)) := by
    rw [hnormal]
    exact contractible_twoPointFrameEmbeddingSpace (f u) (f v) hpair
  have ht : s ∪ {u} ∈ (K.closedFaceStar s).faces :=
    ⟨hu.2.2, by simpa only [← Finset.union_assoc, Finset.union_self] using hu.2.2⟩
  have hframe : (L.frameWithTangent J).range ≤
      (affineSpan ℝ ((s ∪ {u} : Finset E) : Set E)).direction := by
    apply AffineSubspace.normalLineFrame_range_le_direction _ _
      (affineSpan_mono ℝ (show (s : Set E) ⊆ ((s ∪ {u} : Finset E) : Set E) from
        Finset.subset_union_left)) hp
    exact mem_affineSpan ℝ (Finset.mem_union_right s (Finset.mem_singleton_self u))
  have h := K.contractible_faceStarTransversePlaneSpace hK hs hp J hJ ht hframe
  rwa [CommSemiring.finrank_self] at h





theorem contractible_emptyLinkFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) (hlink : (K.faceLink s).faces = ∅) :
    ContractibleSpace (SecantTransversePlaneSpace
      (Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction) (K.closedFaceStar s).space) := by
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ affineSpan ℝ (s : Set E) := mem_affineSpan ℝ hps
  let L := (affineSpan ℝ (s : Set E)).direction
  let f := L.normalAffineProjection p
  have hf : ∀ x ∈ s, f x = 0 := fun x hx =>
    L.normalAffineProjection_eq_zero p
      ((affineSpan ℝ (s : Set E)).vsub_mem_direction (mem_affineSpan ℝ hx) hp)
  let J : (Fin 0 → ℝ) →L[ℝ] ↥(Lᗮ) := 0
  have hJ : Function.Injective J := fun _ _ _ => Subsingleton.elim _ _
  have hnormal : f '' (K.closedFaceStar s).space = {0} :=
    K.affine_image_closedFaceStar_emptyLink hs f hf hlink
  let : ContractibleSpace (FrameEmbeddingSpace J (f '' (K.closedFaceStar s).space)) := by
    rw [hnormal]
    exact contractible_singletonFrameEmbeddingSpace J
  have ht : s ∈ (K.closedFaceStar s).faces := ⟨hs, by simpa only [Finset.union_self] using hs⟩
  have hframe : (L.frameWithTangent J).range ≤ (affineSpan ℝ (s : Set E)).direction :=
    L.frameWithTangent_range_le L J le_rfl (fun _ => L.zero_mem)
  have h := K.contractible_faceStarTransversePlaneSpace hK hs hp J hJ ht hframe
  rwa [Module.finrank_zero_of_subsingleton, zero_add] at h

end PoincareConjecture.M76.Smoothing
