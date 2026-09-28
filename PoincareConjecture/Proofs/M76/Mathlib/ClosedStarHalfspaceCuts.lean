import PoincareConjecture.Proofs.M76.Mathlib.AlignedStarHalfBalls
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
  {ι κ : Type*} [Finite ι] [Nonempty ι] [Finite κ]

theorem isFinitePLBallPair_closedStar_halfspace_cuts
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hz : (0 : E) ∈ K.vertices) (hint : (0 : E) ∈ interior K.space)
    (c : E ≃L[ℝ] (ι → ℝ)) (A : κ → E →ₗ[ℝ] ℝ)
    (hpositive : ∃ v : E, ∀ j, 0 < A j v) :
    IsFinitePLBallPair E
      ((K.closedStar 0).space ∩ {x | ∀ j, 0 ≤ A j x})
      {x | x ∈ (K.closedStar 0).space ∧ (∀ j, 0 ≤ A j x) ∧
        (x ∈ (K.link 0).space ∨ ∃ j, A j x = 0)} := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let L := K.link 0
  have hL : L.faces.Finite := finite_link_faces hK 0
  let N := hL.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ L.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hL.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  let F : Finset (E →ᵃ[ℝ] ℝ) := Finset.univ.image (fun j => (A j).toAffineMap)
  obtain ⟨R, hR, hRL, _, hRA⟩ :=
    L.exists_subdivision_respectsAffineHyperplanes hL hN F
  have hlin := hRL.linearIndependent_faces
    (fun _ hs => linearIndependent_of_mem_link_zero hs)
  have hrad : InjOn (NormedSpace.normalize : E → E) R.space :=
    K.injOn_normalize_link.mono hRL.space_eq.subset
  let J := R.coneAtZero hlin hrad
  have hJ : J.faces.Finite := finite_coneAtZero_faces hR hlin hrad
  have hJstar : J.closedStar 0 = J := R.closedStar_coneAtZero hlin hrad
  have hJlink : (J.link 0).space = (K.link 0).space := by
    rw [show J.link 0 = R from R.link_coneAtZero hlin hrad]
    exact hRL.space_eq
  have hstarint : (0 : E) ∈ interior (K.closedStar 0).space := by
    obtain ⟨ε, hε, hsub⟩ := K.exists_ball_inter_space_subset_closedStar hK hz
    have hV : interior K.space ∩ ball (0 : E) ε ⊆ (K.closedStar 0).space :=
      fun _ hx => hsub ⟨interior_subset hx.1, hx.2⟩
    exact interior_maximal hV (isOpen_interior.inter isOpen_ball)
      ⟨hint, mem_ball_self hε⟩
  have hne : L.space.Nonempty := by
    obtain ⟨C, _, H, hC, _, hC0, _, _, _, hboundary, _⟩ :=
      K.exists_finitePL_closedStar_chart_preserving_halfspaces hK hz hint c
    obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr
      ⟨⟨0, interior_subset hC0⟩, hC.ne_univ⟩
    exact ⟨H.symm ⟨x, hC.isClosed.frontier_subset hx⟩,
      (hboundary _).mpr (by simpa only [H.apply_symm_apply] using hx)⟩
  have hJs : J.space = (K.closedStar 0).space := by
    rw [R.coneAtZero_space_eq_convexJoin hlin hrad (hRL.space_eq.symm ▸ hne),
      hRL.space_eq, ← coneAtZero_link_eq_closedStar K hz]
    exact ((K.link 0).coneAtZero_space_eq_convexJoin
      (fun _ hs => linearIndependent_of_mem_link_zero hs) K.injOn_normalize_link hne).symm
  have hzJ : (0 : E) ∈ J.vertices := zero_mem_coneAtZero_vertices hlin hrad
  have hJA (j : κ) : (J.link 0).RespectsAffineHyperplane (A j).toAffineMap := by
    rw [show J.link 0 = R from R.link_coneAtZero hlin hrad]
    exact hRA _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hresult := J.isFinitePLBallPair_closedStar_inter_halfspaces
    hJ hzJ (hJs.symm ▸ hstarint) c A hJA hpositive
  simpa only [hJstar, hJs, hJlink] using hresult

end Geometry.SimplicialComplex
