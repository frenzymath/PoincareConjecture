import PoincareConjecture.Proofs.M76.Mathlib.CompactConvexHalfspaceNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexNeighborhood

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsCompact.exists_finite_convex_neighborhood_subset
    {C U : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧ Convex ℝ J.space ∧
      C ⊆ interior J.space ∧ J.space ⊆ U := by
  classical
  by_cases hne : C.Nonempty
  · obtain ⟨p, hp⟩ := hne
    rcases subsingleton_or_nontrivial E with hE | hE
    · let : Subsingleton E := hE
      obtain ⟨J, hJ, hJcv, hpJ, hJU⟩ := hU.exists_finite_convex_neighborhood (hCU hp)
      exact ⟨J, hJ, hJcv, fun x _ => (Subsingleton.elim p x) ▸ hpJ, hJU⟩
    · let : Nontrivial E := hE
      let n := Module.finrank ℝ E
      let : NeZero n := ⟨Nat.ne_of_gt Module.finrank_pos⟩
      let c : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
      let f := ContinuousAffineEquiv.constVAdd ℝ E p
      have hpreC : IsCompact (f ⁻¹' C) := f.toHomeomorph.isCompact_preimage.mpr hC
      have hprecv : Convex ℝ (f ⁻¹' C) := hcv.affine_preimage f.toAffineEquiv.toAffineMap
      have hzero : (0 : E) ∈ f ⁻¹' C := by
        change p + 0 ∈ C
        simpa only [add_zero] using hp
      obtain ⟨D, L, _, hD, hDcv, hCD, hDU, _, _, hrep, _, _⟩ :=
        hpreC.exists_convex_halfspace_frontier_neighborhood hprecv hzero
          (hU.preimage f.continuous) (preimage_mono hCU) c
      let F : Finset (E →ᵃ[ℝ] ℝ) :=
        L.image fun A => A.toAffineMap - AffineMap.const ℝ E 1
      have hrep' : D = {x | ∀ A ∈ F, A x ≤ 0} := by
        rw [hrep]
        ext x
        simp only [F, mem_ofPred_eq, Finset.forall_mem_image,
          AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
          AffineMap.const_apply, sub_nonpos]
      obtain ⟨K, hK, hKs⟩ := hD.exists_finite_triangulation_of_halfspaces F hrep'
      have hf := K.affineOnFaces_affine f.toContinuousAffineMap
      let J := hf.embeddedImage f.injective.injOn
      have hJs : J.space = f '' D := by
        rw [hf.embeddedImage_space f.injective.injOn, hKs]
        rfl
      refine ⟨J, hf.embeddedImage_finite f.injective.injOn hK, ?_, ?_, ?_⟩
      · rw [hJs]
        exact hDcv.affine_image f.toAffineEquiv.toAffineMap
      · intro x hx
        have hxpre : f.symm x ∈ f ⁻¹' C := by simpa only [mem_preimage, f.apply_symm_apply] using hx
        rw [hJs]
        change x ∈ interior (f.toHomeomorph '' D)
        rw [← f.toHomeomorph.image_interior]
        exact ⟨f.symm x, hCD hxpre, f.apply_symm_apply x⟩
      · rintro x hx
        obtain ⟨y, hy, rfl⟩ := hJs.subset hx
        exact hDU hy
  · have hCempty : C = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨⊥, ?_, ?_, ?_, ?_⟩ <;>
      simp only [SimplicialComplex.faces_bot, finite_empty, SimplicialComplex.space_bot,
        convex_empty, hCempty, empty_subset]

end Set
