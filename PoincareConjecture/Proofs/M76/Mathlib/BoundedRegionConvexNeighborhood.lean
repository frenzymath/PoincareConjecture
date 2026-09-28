import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood










set_option autoImplicit false

open Set Metric Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsOpen.exists_finite_convex_neighborhood {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
      x ∈ interior K.space ∧ K.space ⊆ U := by
  obtain ⟨K, hK, hcv, hxK⟩ :=
    (isCompact_singleton : IsCompact ({x} : Set E)).exists_finite_convex_neighborhood
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hcompact := (K.isCompact_space_of_finite hK).image
    (continuous_id.sub continuous_const : Continuous (fun y : E => y - x))
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_lt
  let t := ε / (R + 1)
  have ht : 0 < t := div_pos hε (by linarith)
  let H :=
    (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t ht.ne')).toContinuousAffineEquiv
  have hHval (y : E) : H y = t • (y - x) + x := rfl
  have hHx : H x = x := by rw [hHval]; simp
  have hf := K.affineOnFaces_affine H.toContinuousAffineMap
  let L := hf.embeddedImage H.injective.injOn
  have hspace : L.space = H '' K.space := hf.embeddedImage_space H.injective.injOn
  refine ⟨L, hf.embeddedImage_finite H.injective.injOn hK, ?_, ?_, ?_⟩
  · rw [hspace]
    exact hcv.affine_image H.toAffineEquiv.toAffineMap
  · rw [hspace]
    exact H.toHomeomorph.isOpenMap.image_interior_subset K.space
      ⟨x, hxK (mem_singleton x), hHx⟩
  · rw [hspace]
    rintro _ ⟨y, hy, rfl⟩
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hHval, add_sub_cancel_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hyR := hbound (y - x) (mem_image_of_mem (fun z : E => z - x) hy)
    have hmul : t * (R + 1) = ε := div_mul_cancel₀ _ (by linarith : R + 1 ≠ 0)
    nlinarith

end Set
