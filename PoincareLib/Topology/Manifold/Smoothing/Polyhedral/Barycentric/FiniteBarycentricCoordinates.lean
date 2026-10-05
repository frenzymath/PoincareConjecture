import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricRealization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineVertexExtension

/-!+# Barycentric coordinates of arbitrary finite geometric complexes

Simplexwise affine extension of the coordinate vertices gives a
left inverse to barycentric synthesis. Thus global independence
of all geometric vertices is unnecessary. See Hudson 1969,
pp. 12--19, Alexander 1924, p. 6 and M76 derivation 92.
-/

set_option autoImplicit false

open Set Geometry
open scoped BigOperators

namespace StdSimplexCore

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Affine maps commute with barycentric synthesis when the
coordinate sum is one. See Hudson p. 15 and M76 derivation 92. -/
theorem map_barycentricMap (A : E →ᵃ[ℝ] F) (v : ι → E)
    {q : ι → ℝ} (hq : ∑ i, q i = 1) :
    A (barycentricMap v q) = ∑ i, q i • A (v i) := by
  classical
  have h := Finset.univ.map_affineCombination v q hq A
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hq,
    Function.comp_apply, barycentricMap_apply] using h

end StdSimplexCore

namespace Geometry.SimplicialComplex

open StdSimplexCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Coordinate-vertex interpolation is a left inverse to
synthesis on the entire barycentric carrier. This uses the
complex intersection law, not global vertex independence.
See Hudson pp. 15--19 and M76 derivation 92. -/
theorem exists_barycentric_leftInverse (K : SimplicialComplex ℝ E)
    [Fintype K.vertices] :
    ∃ f : E → (K.vertices → ℝ), K.AffineOnFaces f ∧
      LeftInvOn f (barycentricMap ((↑) : K.vertices → E))
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace := by
  classical
  let v : E → (K.vertices → ℝ) := Function.extend ((↑) : K.vertices → E)
    (fun i => Pi.single i 1) (fun _ => 0)
  obtain ⟨f, hf, hfv⟩ := K.exists_affineOnFaces_eqOn_vertices v
  have hv (i : K.vertices) : f i = Pi.single i 1 := by
    rw [hfv i.property]
    exact Subtype.val_injective.extend_apply _ _ i
  refine ⟨f, hf, ?_⟩
  intro q hq
  obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.mp hq
  obtain ⟨a, ha⟩ := hf (s.map (Function.Embedding.subtype _)) hs
  have hx : barycentricMap ((↑) : K.vertices → E) q ∈
      convexHull ℝ ((s.map (Function.Embedding.subtype _)) : Set E) := by
    rw [Finset.coe_map, Function.Embedding.coe_subtype, ← image_barycentricFace]
    exact mem_image_of_mem _ hqs
  rw [ha hx]
  change a.toAffineMap (barycentricMap ((↑) : K.vertices → E) q) = q
  rw [map_barycentricMap a.toAffineMap _ hqs.1.2]
  change (∑ i : K.vertices, q i • a (i : E)) = q
  have hsum : (∑ i : K.vertices, q i • a (i : E)) = ∑ i, q i • Pi.single i 1 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ s
    · have his : (i : E) ∈ s.map (Function.Embedding.subtype _) :=
        Finset.mem_map.mpr ⟨i, hi, rfl⟩
      rw [← ha (subset_convexHull ℝ _ his), hv]
    · rw [hqs.2 i hi, zero_smul, zero_smul]
  rw [hsum]
  ext i
  simp [Pi.single_apply, Pi.smul_apply, Finset.sum_apply]

/-- Barycentric synthesis on a finite geometric complex is
injective without a global vertex-independence premise.
See Hudson pp. 15--19 and M76 derivation 92. -/
theorem injOn_barycentricMap_vertexComplex (K : SimplicialComplex ℝ E)
    [Fintype K.vertices] :
    InjOn (barycentricMap ((↑) : K.vertices → E))
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace := by
  obtain ⟨_, _, hleft⟩ := K.exists_barycentric_leftInverse
  exact hleft.injOn

/-- The actual geometric carrier is homeomorphic to its finite
barycentric realization, retaining the original subspace topology.
Empty complexes are included. See Hudson pp. 15--19 and M76
derivation 92. -/
noncomputable def finiteBarycentricHomeomorph (K : SimplicialComplex ℝ E)
    [Fintype K.vertices] :
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace ≃ₜ K.space := by
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let v := ((↑) : K.vertices → E)
  let : CompactSpace A.barycentricSpace :=
    isCompact_iff_compactSpace.mp A.isCompact_barycentricSpace
  let e : A.barycentricSpace ≃ₜ barycentricMap v '' A.barycentricSpace :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn (barycentricMap v) A.barycentricSpace
        K.injOn_barycentricMap_vertexComplex)
      (((barycentricMap v).continuous.comp continuous_subtype_val).subtype_mk _)
  exact e.trans (Homeomorph.setCongr K.image_barycentricSpace)

/-- The realization homeomorphism is the original weighted
vertex sum. See Hudson p. 15 and M76 derivation 92. -/
theorem finiteBarycentricHomeomorph_apply (K : SimplicialComplex ℝ E)
    [Fintype K.vertices]
    (q : K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace) :
    (K.finiteBarycentricHomeomorph q : E) = barycentricMap ((↑) : K.vertices → E) q := rfl

end Geometry.SimplicialComplex
