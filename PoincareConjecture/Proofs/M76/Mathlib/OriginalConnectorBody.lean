import PoincareConjecture.Proofs.M76.Mathlib.CompactConvexHalfspaceNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_open_maximal_face_interior_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s) :
    ∃ U : Set E, IsOpen U ∧
      intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ⊆ U ∧
      (∀ t ∈ K.faces, (convexHull ℝ (t : Set E) ∩ U).Nonempty → t = s) ∧
      Disjoint U (intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) := by
  let T := {t : Finset E | t ∈ K.faces ∧ t ≠ s}
  have hT : T.Finite := hK.subset fun _ ht => ht.1
  let D := ⋃ t ∈ T, convexHull ℝ (t : Set E)
  have hD : IsClosed D :=
    (hT.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
  let F := intrinsicFrontier ℝ (convexHull ℝ (s : Set E))
  have hF : IsClosed F := isClosed_intrinsicFrontier
    (affineSpan ℝ (convexHull ℝ (s : Set E))).closed_of_finiteDimensional
  let U := Dᶜ ∩ Fᶜ
  refine ⟨U, hD.isOpen_compl.inter hF.isOpen_compl, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro hxD
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxD
      exact ht.2 (hmax t ht.1 (K.subset_of_mem_intrinsicInterior_face hs ht.1 hx hxt))
    · intro hxF
      change x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) at hxF
      rw [← intrinsicClosure_sdiff_intrinsicInterior] at hxF
      exact hxF.2 hx
  · intro t ht hmeet
    by_contra hts
    obtain ⟨x, hxt, hxU⟩ := hmeet
    exact hxU.1 (mem_iUnion₂.mpr ⟨t, ⟨ht, hts⟩, hxt⟩)
  · exact disjoint_left.mpr fun _ hxU hxF => hxU.2 hxF

theorem exists_compact_convex_maximal_face_body [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s)
    {S W : Set E} (hS : IsCompact S) (hcvS : Convex ℝ S) (hzeroS : (0 : E) ∈ S)
    (hSin : S ⊆ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hW : IsOpen W) (hSW : S ⊆ W)
    (M : SimplicialComplex ℝ E) (hMK : M.space = K.space)
    (hstar : (M.closedStar 0).space = convexHull ℝ (s : Set E))
    (hlink : (M.link 0).space = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    {ι : Type*} [Finite ι] [Nonempty ι] (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ (C : Set E) (L : Finset (E →ₗ[ℝ] ℝ)) (J : SimplicialComplex ℝ E),
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧
      S ⊆ interior C ∧ C ⊆ W ∧ Disjoint C (M.link 0).space ∧
      M.space ∩ C = (M.closedStar 0).space ∩ C ∧
      (∀ t ∈ K.faces, (convexHull ℝ (t : Set E) ∩ C).Nonempty →
        (0 : E) ∈ convexHull ℝ (t : Set E)) ∧
      L.Nonempty ∧ (∀ A ∈ L, A ≠ 0) ∧ C = {x | ∀ A ∈ L, A x ≤ 1} ∧
      J.faces.Finite ∧ J.space = frontier C := by
  obtain ⟨U, hU, hSU, hface, hfront⟩ :=
    K.exists_open_maximal_face_interior_neighborhood hK hs hmax
  obtain ⟨C, L, J, hC, hcv, hSC, hCUW, hLne, hL, hrep, hJ, hJC⟩ :=
    hS.exists_convex_halfspace_frontier_neighborhood hcvS hzeroS
      (hU.inter hW) (fun _ hx => ⟨hSU (hSin hx), hSW hx⟩) c
  have hCU : C ⊆ U := hCUW.trans inter_subset_left
  have hfaceC (t : Finset E) (ht : t ∈ K.faces)
      (hmeet : (convexHull ℝ (t : Set E) ∩ C).Nonempty) : t = s := by
    obtain ⟨x, hxt, hxC⟩ := hmeet
    exact hface t ht ⟨x, hxt, hCU hxC⟩
  have hdisj : Disjoint C (M.link 0).space := by
    rw [hlink]
    exact hfront.mono_left hCU
  have hlocal : M.space ∩ C = (M.closedStar 0).space ∩ C := by
    rw [hMK, hstar]
    ext x
    constructor
    · rintro ⟨hxK, hxC⟩
      obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxK
      exact ⟨hfaceC t ht ⟨x, hxt, hxC⟩ ▸ hxt, hxC⟩
    · rintro ⟨hxs, hxC⟩
      exact ⟨K.convexHull_subset_space hs hxs, hxC⟩
  refine ⟨C, L, J, hC, hcv, hSC hzeroS, hSC,
    hCUW.trans inter_subset_right, hdisj, hlocal, ?_, hLne, hL, hrep, hJ, hJC⟩
  intro t ht hmeet
  rw [hfaceC t ht hmeet]
  exact intrinsicInterior_subset (hSin hzeroS)

end Geometry.SimplicialComplex
