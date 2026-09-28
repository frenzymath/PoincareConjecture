import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineSectionFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry

set_option autoImplicit false

open Set

namespace Geometry

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Finite ι]

theorem isFinitePLBallPair_convex_affine_section
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (L : ι → E →ₗ[ℝ] ℝ)
    (hrep : C = {x | ∀ i, L i x ≤ 1})
    (a : F →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] F)
    (hleft : Function.LeftInverse r a) (ha0 : a 0 = 0) :
    IsFinitePLBallPair F (C ∩ range a) (frontier C ∩ range a) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hright : LeftInvOn a r (range a) := by
    rintro x ⟨y, rfl⟩
    rw [hleft y]
  have hrange : range a = {x | a (r x) = x} := by
    ext x
    exact ⟨fun hx => hright hx, fun hx => ⟨r x, hx⟩⟩
  have hclosed : IsClosed (range a) := by
    rw [hrange]
    exact isClosed_eq (a.continuous.comp r.continuous) continuous_id
  have himage : r '' (C ∩ range a) = a ⁻¹' C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change a (r x) ∈ C
      rw [hright hx.2]
      exact hx.1
    · intro hy
      exact ⟨a y, ⟨hy, mem_range_self y⟩, hleft y⟩
  have hCp : IsCompact (a ⁻¹' C) := himage ▸ (hC.inter_right hclosed).image r.continuous
  have hcvp : Convex ℝ (a ⁻¹' C) := hcv.affine_preimage a.toAffineMap
  have hz : (0 : F) ∈ interior (a ⁻¹' C) := by
    apply preimage_interior_subset_interior_preimage a.continuous
    change a 0 ∈ interior C
    rwa [ha0]
  let forms : Finset (F →ᵃ[ℝ] ℝ) := Finset.univ.image
    (fun i => (L i).toAffineMap.comp a.toAffineMap - AffineMap.const ℝ F 1)
  have hforms : a ⁻¹' C = {x | ∀ A ∈ forms, A x ≤ 0} := by
    ext x
    simp only [mem_preimage, hrep, mem_ofPred_eq, forms, Finset.mem_image,
      Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff,
      AffineMap.coe_sub, Pi.sub_apply, AffineMap.comp_apply, AffineMap.const_apply,
      LinearMap.coe_toAffineMap, sub_nonpos]
    rfl
  obtain ⟨K, hK, hKs⟩ := hCp.exists_finite_triangulation_of_halfspaces forms hforms
  have hball := isFinitePLBallPair_of_compact_convex hCp hcvp ⟨0, hz⟩ K hK hKs
  have h := hball.affine_image a hleft.injective.injOn
  rwa [a.frontier_preimage_convex hC.isClosed hcv ⟨0, ha0.symm ▸ hzero⟩,
    image_preimage_eq_inter_range, image_preimage_eq_inter_range] at h

end Geometry
