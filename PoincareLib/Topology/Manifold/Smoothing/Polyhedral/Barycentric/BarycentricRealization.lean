import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricCoreComplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.VertexAbstractComplex

/-!
# The barycentric realization homeomorphism

Summing the weighted actual vertices identifies the compact
barycentric carrier with an independent geometric complex in its
original topology. See Cairns 1940, pp. 798--799, 804, and M76
derivation 50.
-/

set_option autoImplicit false

open Set Geometry

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A face simplex is the image of its own standard simplex by
zero extension. See Cairns pp. 802--803 and M76 derivation 50. -/
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
/-- Zero extension carries a face vertex to its matching global
barycentric vertex. See Cairns pp. 802--803 and M76 derivation 50. -/
theorem faceInclusion_single (s : Finset ι) (i : s) :
    faceInclusion s (Pi.single i 1) = Pi.single i.val 1 := by
  ext j
  by_cases hj : j ∈ s
  · rw [faceInclusion_apply_mem s _ hj]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · rw [faceInclusion_apply_notMem s _ hj]
    have hne : i.val ≠ j := fun he => hj (he ▸ i.property)
    simp [hne]

/-- The global face simplex is the convex hull of its labelled
coordinate vertices. See Cairns pp. 802--803 and M76 derivation 50. -/
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

/-- Finite barycentric synthesis into the actual vertex positions.
See Cairns pp. 798--799 and M76 derivation 50. -/
noncomputable def barycentricMap (v : ι → E) : (ι → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

omit [DecidableEq ι] in
/-- Barycentric synthesis is the weighted sum of actual vertices.
See Cairns pp. 798--799 and M76 derivation 50. -/
theorem barycentricMap_apply (v : ι → E) (q : ι → ℝ) :
    barycentricMap v q = ∑ i, q i • v i := by
  simp only [barycentricMap, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- Coordinate vertices synthesize to the actual vertices.
See Cairns pp. 798--799 and M76 derivation 50. -/
theorem barycentricMap_single (v : ι → E) (i : ι) : barycentricMap v (Pi.single i 1) = v i := by
  simp [barycentricMap_apply, Pi.single_apply, ite_smul]

omit [DecidableEq ι] in
/-- Synthesis maps a face onto the convex hull of its actual
vertices. See Cairns pp. 798--799 and M76 derivation 50. -/
theorem image_barycentricFace (v : ι → E) (s : Finset ι) :
    barycentricMap v '' barycentricFace s = convexHull ℝ (v '' (s : Set ι)) := by
  classical
  rw [barycentricFace_eq_convexHull]
  change (barycentricMap v).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull, image_image]
  change convexHull ℝ ((fun i => barycentricMap v (Pi.single i 1)) '' (s : Set ι)) = _
  simp only [barycentricMap_single]

omit [DecidableEq ι] in
/-- Affine independence gives unique barycentric coordinates on
the standard simplex. See Cairns p. 798 and M76 derivation 50. -/
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

/-- Synthesis of the actual vertex labels maps the entire
barycentric carrier onto the geometric carrier.
See Cairns pp. 798--799 and M76 derivation 50. -/
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

/-- An independent finite geometric complex is homeomorphic to
the barycentric carrier on its actual vertices, including the
empty complex. See Cairns p. 798 and M76 derivation 50. -/
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

/-- The realization homeomorphism retains the explicit barycentric
formula. See Cairns p. 798 and M76 derivation 50. -/
theorem barycentricHomeomorph_apply (K : SimplicialComplex ℝ E) [Fintype K.vertices]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    (q : K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace) :
    (K.barycentricHomeomorph hK q : E) = barycentricMap ((↑) : K.vertices → E) q := rfl

end Geometry.SimplicialComplex
