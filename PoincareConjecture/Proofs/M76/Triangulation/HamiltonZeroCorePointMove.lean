import PoincareConjecture.Proofs.M76.Mathlib.ConvexFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry
import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization
import PoincareConjecture.Proofs.M76.Mathlib.ClosedBallIsotopy











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

private theorem exists_pointed_convex_selfmap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsCompact S) (hcv : Convex ℝ S)
    (h0 : (0 : E) ∈ interior S) {z : E} (hz : z ∈ interior S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKs : K.space = S) :
    ∃ H : S ≃ₜ S, H.IsFinitePL ∧
      (H ⟨0, interior_subset h0⟩ : E) = z ∧
      ∀ x : S, (x : E) ∈ frontier S → H x = x := by
  classical
  let B := K.frontierSubcomplex S
  have hB : B.faces.Finite := K.frontierSubcomplex_finite S hK
  have hBs : B.space = frontier S :=
    K.frontierSubcomplex_space hS.isClosed hcv ⟨0, h0⟩ hKs
  let a : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-z)
  have ha0 : a z = 0 := by change -z + z = 0; exact neg_add_cancel z
  have hT : IsCompact (a '' S) := hS.image a.continuous
  have hTcv : Convex ℝ (a '' S) := hcv.affine_image a.toAffineEquiv.toAffineMap
  have hT0 : (0 : E) ∈ interior (a '' S) := by
    change (0 : E) ∈ interior (a.toHomeomorph '' S)
    rw [← a.toHomeomorph.image_interior]
    exact ⟨z, hz, ha0⟩
  let hf := B.affineOnFaces_affine a.toContinuousAffineMap
  let L := hf.embeddedImage a.injective.injOn
  have hLs : L.space = frontier (a '' S) := by
    rw [show L.space = a '' B.space by
      exact hf.embeddedImage_space a.injective.injOn]
    rw [hBs]
    exact a.toHomeomorph.image_frontier S
  have hlinB := B.linearIndependent_faces_of_space_subset_frontier hcv h0 hBs.subset
  have hradB : InjOn (NormedSpace.normalize : E → E) B.space := by
    rw [hBs]
    exact hcv.injOn_normalize_frontier h0
  have hlinL := L.linearIndependent_faces_of_space_subset_frontier hTcv hT0 hLs.subset
  have hradL : InjOn (NormedSpace.normalize : E → E) L.space := by
    rw [hLs]
    exact hTcv.injOn_normalize_frontier hT0
  have hconeB := B.coneAtZero_space_of_frontier hlinB hradB hS hcv h0 hBs
  have hconeL := L.coneAtZero_space_of_frontier hlinL hradL hT hTcv hT0 hLs
  obtain ⟨f, H, hfPL, hf0, hfbase, hH⟩ :=
    hf.exists_cone_extension_affine a.injective.injOn hB hlinB hradB hlinL hradL
  let G : S ≃ₜ S := (Homeomorph.setCongr hconeB.symm).trans
    (H.trans ((Homeomorph.setCongr hconeL).trans (a.toHomeomorph.image S).symm))
  have hG (x : S) : (G x : E) = a.symm (f x) := by
    change a.symm (H ⟨x, hconeB.symm ▸ x.property⟩) = a.symm (f x)
    rw [hH]
  have hGPl : G.IsFinitePL := by
    refine ⟨a.symm ∘ f, ?_, hG⟩
    have h := (hfPL.finitePiecewiseAffineOn
      (SimplicialComplex.finite_coneAtZero_faces hB hlinB hradB)).postcomp
        a.symm.toContinuousAffineMap
    rwa [hconeB] at h
  refine ⟨G, hGPl, ?_, ?_⟩
  · rw [hG, hf0, ← ha0, a.symm_apply_apply]
  · intro x hx
    apply Subtype.ext
    rw [hG, hfbase (hBs.symm ▸ hx)]
    change a.symm (a (x : E)) = x
    rw [a.symm_apply_apply]

private theorem exists_radius_two_cube_complex {ι : Type*} [Fintype ι] :
    ∃ K : SimplicialComplex ℝ (ι → ℝ), K.faces.Finite ∧
      K.space = closedBall (0 : ι → ℝ) 2 := by
  classical
  let A : ι ⊕ ι → (ι → ℝ) →ᵃ[ℝ] ℝ := fun i =>
    (signedCubeCoordinate i).toAffineMap - AffineMap.const ℝ (ι → ℝ) 2
  let H := Finset.univ.image A
  have hrep : closedBall (0 : ι → ℝ) 2 = {x | ∀ a ∈ H, a x ≤ 0} := by
    ext x
    rw [mem_closedBall_zero_iff]
    constructor
    · intro hx a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      change signedCubeCoordinate i x - 2 ≤ 0
      exact sub_nonpos.mpr ((signedCubeCoordinate_le_norm i x).trans hx)
    · intro hx
      have hb (i : ι ⊕ ι) : signedCubeCoordinate i x ≤ 2 := by
        have h := hx (A i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        exact sub_nonpos.mp h
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro i
      rw [Real.norm_eq_abs]
      have hp : x i ≤ 2 := hb (.inl i)
      have hn : -x i ≤ 2 := hb (.inr i)
      exact abs_le.mpr ⟨by linarith, hp⟩
  exact (isCompact_closedBall _ _).exists_finite_triangulation_of_halfspaces H hrep




theorem exists_supported_finitePL_cube_point_move {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (hz : ‖z‖ < 2) :
    ∃ M : (ι → ℝ) ≃ₜ (ι → ℝ),
      FinitePiecewiseAffineOn M (closedBall (0 : ι → ℝ) 2) ∧ M 0 = z ∧
      ∀ x, 2 ≤ ‖x‖ → M x = x := by
  obtain ⟨K, hK, hKs⟩ := exists_radius_two_cube_complex (ι := ι)
  have h0 : (0 : ι → ℝ) ∈ interior (closedBall (0 : ι → ℝ) 2) :=
    ball_subset_interior_closedBall (mem_ball_self (by norm_num))
  have hz' : z ∈ interior (closedBall (0 : ι → ℝ) 2) :=
    ball_subset_interior_closedBall (mem_ball_zero_iff.mpr hz)
  obtain ⟨H, ⟨f, hf, hHf⟩, hH0, hHfront⟩ :=
    exists_pointed_convex_selfmap (isCompact_closedBall _ _) (convex_closedBall _ _)
      h0 hz' K hK hKs
  have hfix (x : closedBall (0 : ι → ℝ) 2) (hx : ‖(x : ι → ℝ)‖ = 2) : H x = x := by
    apply hHfront
    rw [frontier_closedBall _ (by norm_num : (2 : ℝ) ≠ 0)]
    simpa only [mem_sphere, dist_zero_right] using hx
  let M := H.closedBallExtension hfix
  refine ⟨M, hf.congr ?_, ?_, H.closedBallExtension_fixed_outside hfix⟩
  · intro x hx
    exact (hHf ⟨x, hx⟩).symm.trans (H.closedBallExtension_apply_mem hfix hx).symm
  · change H.closedBallExtension hfix 0 = z
    rw [H.closedBallExtension_apply_mem hfix (interior_subset h0)]
    exact hH0

end PoincareConjecture.M76
