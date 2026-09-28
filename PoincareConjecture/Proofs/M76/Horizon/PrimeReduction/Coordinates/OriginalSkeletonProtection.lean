import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AffineTriangleComponents
import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningArcProtection









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem original_skeleton_triangle_intersection_subset_boundary
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {x : V3} (hx : x ∈ convexHull ℝ (A '' (s : Set E)))
    (hxsk : Q.symm x ∈ ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
      g '' convexHull ℝ (a : Set E)) :
    x ∈ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) := by
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro u hu v hv heq
    exact hgi (K.convexHull_subset_space hs hu) (K.convexHull_subset_space hs hv)
      (Q.injOn (hmap hu) (hmap hv) ((hA hu).trans (heq.trans (hA hv).symm)))
  obtain ⟨u, hu, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
  have hQu : Q.symm (A u) = g u := by rw [← hA hu]; exact Q.left_inv (hmap hu)
  change Q.symm (A u) ∈ _ at hxsk
  rw [hQu] at hxsk
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxsk
  obtain ⟨ha2, v, hv, heq⟩ := mem_iUnion.mp hxa
  have hvu : v = u := hgi (K.convexHull_subset_space ha hv) (K.convexHull_subset_space hs hu) heq
  have huint : u ∉ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    intro hint
    have hsub := K.subset_of_mem_intrinsicInterior_face hs ha hint (hvu ▸ hv)
    have hcard := Finset.card_le_card hsub
    omega
  have hufront : u ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hu, huint⟩
  have hAsp := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hAi
  change A.toAffineMap u ∈ intrinsicFrontier ℝ (convexHull ℝ (A.toAffineMap '' (s : Set E)))
  rw [← A.toAffineMap.image_convexHull]
  rw [A.toAffineMap.intrinsicFrontier_image_of_injOn _ hAsp]
  exact mem_image_of_mem A hufront



theorem exists_original_skeleton_coordinate_protection
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    {Z : Set V3} (hZ : IsClosed Z)
    (hfront : frontier J.space ⊆ Z)
    (hboundary : intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) ⊆ Z) :
    ∃ C : Set V3, IsClosed C ∧ Z ⊆ C ∧ frontier J.space ⊆ C ∧
      (J.space ∩ Q.symm ⁻¹' (⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
        g '' convexHull ℝ (a : Set E))) ⊆ C ∧
      C ∩ convexHull ℝ (A '' (s : Set E)) = Z ∩ convexHull ℝ (A '' (s : Set E)) := by
  classical
  let E₁ : Set X := ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2), g '' convexHull ℝ (a : Set E)
  have hE₁ : IsClosed E₁ := hK.isClosed_biUnion fun a ha => isClosed_iUnion_of_finite
    fun _ => ((a.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hgc.mono (K.convexHull_subset_space ha))).isClosed
  let C := Z ∪ (J.space ∩ Q.symm ⁻¹' E₁)
  have hC : IsClosed C := hZ.union ((Q.symm.continuousOn.mono hJQ).preimage_isClosed_of_isClosed
    (J.isCompact_space_of_finite hJ).isClosed hE₁)
  refine ⟨C, hC, subset_union_left, hfront.trans subset_union_left, subset_union_right, ?_⟩
  ext x
  constructor
  · rintro ⟨hxC, hxt⟩
    rcases hxC with hxZ | hxE₁
    · exact ⟨hxZ, hxt⟩
    · exact ⟨hboundary (original_skeleton_triangle_intersection_subset_boundary K g hgi hs hs3
        Q A hmap hA hxt hxE₁.2), hxt⟩
  · exact fun hx => ⟨Or.inl hx.1, hx.2⟩

end PoincareConjecture.M76
