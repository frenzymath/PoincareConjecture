import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicFaceSaturation










set_option autoImplicit false

open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsSecantTransverse.disjoint_affineDirection {P : Submodule ℝ E} {S C : Set E}
    (hP : P.IsSecantTransverse S) (hC : Convex ℝ C) (hne : C.Nonempty) (hCS : C ⊆ S) :
    Disjoint (affineSpan ℝ C).direction P := by
  obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior hC hne
  obtain ⟨c, hc, hb⟩ := hP
  apply Submodule.disjoint_def.mpr
  intro x hx hxp
  obtain ⟨r, hr, hrp⟩ := exists_pos_smul_add_mem_of_intrinsicInterior hp hx
  have h := hb _ (hCS hrp) p (hCS (intrinsicInterior_subset hp))
  rw [add_sub_cancel_right,
    P.starProjection_eq_self_iff.mpr (P.smul_mem r hxp), sub_self, norm_zero] at h
  have hn : ‖r • x‖ = 0 := by nlinarith only [h, hc, norm_nonneg (r • x)]
  exact (smul_eq_zero.mp (norm_eq_zero.mp hn)).resolve_left hr.ne'

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem disjoint_faceDirection_of_isSecantTransverse (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {P : Submodule ℝ E}
    (hP : P.IsSecantTransverse K.space) :
    Disjoint (affineSpan ℝ (s : Set E)).direction P := by
  have hne := (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull (𝕜 := ℝ)
  simpa only [affineSpan_convexHull] using hP.disjoint_affineDirection
    (convex_convexHull ℝ _) hne (convexHull_subset_space hs)

end Geometry.SimplicialComplex
