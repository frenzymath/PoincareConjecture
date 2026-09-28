import PoincareConjecture.Proofs.M76.Mathlib.BarycentricCoreComplex
import PoincareConjecture.Proofs.M76.Mathlib.VertexAbstractComplex










set_option autoImplicit false

open Set Geometry

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



theorem barycentricFace_eq_image (s : Finset ι) :
    barycentricFace s = faceInclusion s '' stdSimplex ℝ s := by
  apply Subset.antisymm
  · intro q hq
    let r : s → ℝ := fun i => q i
    have he : faceInclusion s r = q := by
      ext i
      by_cases hi : i ∈ s
      · exact faceInclusion_apply_mem s r hi
      · rw [faceInclusion_apply_notMem s r hi, hq.2 i hi]
    refine ⟨r, ⟨fun i => hq.1.1 i, ?_⟩, he⟩
    rw [← sum_faceInclusion s r, he]
    exact hq.1.2
  · rintro _ ⟨q, hq, rfl⟩
    exact faceInclusion_mem_barycentricFace s (le_refl (0 : ℝ)) hq

omit [Fintype ι] in


theorem faceInclusion_single (s : Finset ι) (i : s) :
    faceInclusion s (Pi.single i 1) = Pi.single i.val 1 := by
  ext j
  by_cases hj : j ∈ s
  · rw [faceInclusion_apply_mem s _ hj]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · rw [faceInclusion_apply_notMem s _ hj]
    have hne : i.val ≠ j := fun he => hj (he ▸ i.property)
    simp [hne]



theorem barycentricFace_eq_convexHull (s : Finset ι) :
    barycentricFace s = convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (s : Set ι)) := by
  rw [barycentricFace_eq_image, ← convexHull_rangle_single_eq_stdSimplex ℝ s]
  change (faceInclusion s).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull, ← range_comp]
  congr 1
  ext q
  change (∃ i : s, faceInclusion s (Pi.single i 1) = q) ↔ ∃ i ∈ s, Pi.single i 1 = q
  simp only [faceInclusion_single, Subtype.exists, exists_prop]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def barycentricMap (v : ι → E) : (ι → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

omit [DecidableEq ι] in


theorem barycentricMap_apply (v : ι → E) (q : ι → ℝ) :
    barycentricMap v q = ∑ i, q i • v i := by
  simp only [barycentricMap, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]



theorem barycentricMap_single (v : ι → E) (i : ι) : barycentricMap v (Pi.single i 1) = v i := by
  simp [barycentricMap_apply, Pi.single_apply, ite_smul]

omit [DecidableEq ι] in


theorem image_barycentricFace (v : ι → E) (s : Finset ι) :
    barycentricMap v '' barycentricFace s = convexHull ℝ (v '' (s : Set ι)) := by
  classical
  rw [barycentricFace_eq_convexHull]
  change (barycentricMap v).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull, image_image]
  change convexHull ℝ ((fun i => barycentricMap v (Pi.single i 1)) '' (s : Set ι)) = _
  simp only [barycentricMap_single]

omit [DecidableEq ι] in


theorem injOn_barycentricMap (v : ι → E) (hv : AffineIndependent ℝ v) :
    InjOn (barycentricMap v) (stdSimplex ℝ ι) := by
  intro q hq r hr he
  funext i
  exact hv.eq_of_sum_eq_sum (hq.2.trans hr.2.symm)
    (by simpa only [barycentricMap_apply] using he) i (Finset.mem_univ i)

end StdSimplexCore

namespace Geometry.SimplicialComplex

open StdSimplexCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem image_barycentricSpace (K : SimplicialComplex ℝ E) [Fintype K.vertices] :
    barycentricMap ((↑) : K.vertices → E) ''
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace = K.space := by
  classical
  apply Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.mp hq
    refine mem_space_iff.mpr ⟨s.map (Function.Embedding.subtype _), hs, ?_⟩
    rw [Finset.coe_map, Function.Embedding.coe_subtype,
      ← image_barycentricFace ((↑) : K.vertices → E) s]
    exact mem_image_of_mem _ hqs
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨s, hs, he⟩ := K.faces_eq_vertexAbstractComplex_images ▸ ht
    rw [he, ← image_barycentricFace ((↑) : K.vertices → E) s] at hxt
    obtain ⟨q, hq, rfl⟩ := hxt
    exact ⟨q, mem_iUnion₂.mpr ⟨s, hs, hq⟩, rfl⟩




noncomputable def barycentricHomeomorph (K : SimplicialComplex ℝ E) [Fintype K.vertices]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) :
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace ≃ₜ K.space := by
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let v := ((↑) : K.vertices → E)
  have hinj : InjOn (barycentricMap v) A.barycentricSpace :=
    (injOn_barycentricMap v hK).mono (by
      intro q hq
      obtain ⟨s, _, hqs⟩ := mem_iUnion₂.mp hq
      exact hqs.1)
  let : CompactSpace A.barycentricSpace :=
    isCompact_iff_compactSpace.mp A.isCompact_barycentricSpace
  let e : A.barycentricSpace ≃ₜ barycentricMap v '' A.barycentricSpace :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn (barycentricMap v) A.barycentricSpace hinj)
      (((barycentricMap v).continuous.comp continuous_subtype_val).subtype_mk _)
  exact e.trans (Homeomorph.setCongr K.image_barycentricSpace)



theorem barycentricHomeomorph_apply (K : SimplicialComplex ℝ E) [Fintype K.vertices]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    (q : K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace) :
    (K.barycentricHomeomorph hK q : E) = barycentricMap ((↑) : K.vertices → E) q := rfl

end Geometry.SimplicialComplex
