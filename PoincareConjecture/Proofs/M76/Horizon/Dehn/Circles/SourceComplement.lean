import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralFrontierRegion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections











set_option autoImplicit false

open Set Metric Geometry

namespace Dehn

private theorem closed_hole_complement {E : Type*} [TopologicalSpace E]
    {S A : Set E} (hS : IsClosed S) (hA : IsClosed A)
    (hSreg : closure (interior S) = S) (hAreg : closure (interior A) = A)
    (hAS : A ⊆ interior S) :
    closure (interior (S \ interior A)) = S \ interior A ∧
      frontier (S \ interior A) = frontier S ∪ frontier A := by
  have hi : interior (S \ interior A) = interior S \ A := by
    simp only [sdiff_eq, interior_inter, interior_compl, hAreg]
  have hclosed : IsClosed (S \ interior A) := hS.sdiff isOpen_interior
  have hreg : closure (interior (S \ interior A)) = S \ interior A := by
    apply Subset.antisymm (closure_minimal interior_subset hclosed)
    intro x hx
    rw [hi]
    by_cases hxS : x ∈ interior S
    · have hxcl : x ∈ closure (Aᶜ) := by
        rw [closure_compl]
        exact hx.2
      have h := isOpen_interior.closure_inter (s := Aᶜ) ⟨hxcl, hxS⟩
      simpa only [inter_comm, Set.sdiff_eq] using h
    · have hxA : x ∉ A := fun h => hxS (hAS h)
      exact hA.isOpen_compl.closure_inter ⟨hSreg.symm ▸ hx.1, hxA⟩
  refine ⟨hreg, ?_⟩
  rw [frontier, hclosed.closure_eq, hi, frontier, hS.closure_eq, frontier, hA.closure_eq]
  ext x
  constructor
  · rintro ⟨⟨hxS, hxAi⟩, hxnot⟩
    by_cases hxSi : x ∈ interior S
    · exact Or.inr ⟨by by_contra hxA; exact hxnot ⟨hxSi, hxA⟩, hxAi⟩
    · exact Or.inl ⟨hxS, hxSi⟩
  · rintro (⟨hxS, hxSi⟩ | ⟨hxA, hxAi⟩)
    · exact ⟨⟨hxS, fun h => hxSi (hAS (interior_subset h))⟩, fun h => hxSi h.1⟩
    · exact ⟨⟨interior_subset (hAS hxA), hxAi⟩, fun h => h.2 hxA⟩

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1



theorem exists_polygon_source_complement {n : ℕ} (P : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) :
    frontier (D \ P.inside) = R ∪ P.boundary ℝ ∧
      ∃ K : SimplicialComplex ℝ V2, K.faces.Finite ∧ K.space = D \ P.inside := by
  obtain ⟨_, hiP, hfP, hsP⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
  have hDreg : closure (interior D) = D := by
    rw [interior_closedBall _ one_ne_zero, closure_ball _ one_ne_zero]
  have hPreg : closure (interior (closure P.inside)) = closure P.inside := by rw [hiP]
  have hPD : closure P.inside ⊆ interior D := by
    rw [interior_closedBall _ one_ne_zero]
    exact hsP
  obtain ⟨hreg, hf⟩ := closed_hole_complement isClosed_closedBall isClosed_closure
    hDreg hPreg hPD
  rw [hiP] at hreg hf
  rw [frontier_closedBall _ one_ne_zero, hfP] at hf
  refine ⟨hf, ?_⟩
  let U := PoincareConjecture.M76.Dehn.squareRimPolygon
  have hU : U.HasSimplicialEdges := PoincareConjecture.M76.Dehn.hasSimplicialEdges_squareRimPolygon
  obtain ⟨J, hJ, hJs⟩ := (U.simplicialComplex hU).exists_finite_triangulation_union
    (P.simplicialComplex hP) (U.finite_simplicialComplex_faces hU)
    (P.finite_simplicialComplex_faces hP)
  have hfront : J.space = frontier (D \ P.inside) := by
    rw [hJs, U.simplicialComplex_space hU, P.simplicialComplex_space hP, hf]
    exact congrArg (fun s => s ∪ P.boundary ℝ) PoincareConjecture.M76.Dehn.boundary_squareRimPolygon
  have hclosed : IsClosed (D \ P.inside) := by
    rw [← hiP]
    exact isClosed_closedBall.sdiff isOpen_interior
  obtain ⟨K, _, hK, _, hKs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_of_polyhedral_frontier
      ((isCompact_closedBall (0 : V2) 1).of_isClosed_subset hclosed sdiff_subset)
      hreg J hJ hfront
  exact ⟨K, hK, hKs⟩




theorem exists_two_polygon_source_complement {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) (hQsq : Q.boundary ℝ ⊆ ball 0 1) :
    ∃ K : SimplicialComplex ℝ V2, K.faces.Finite ∧
      K.space = D \ (P.inside ∪ Q.inside) := by
  obtain ⟨_, K, hK, hKs⟩ := exists_polygon_source_complement P hP hinjP hPsq
  obtain ⟨_, L, hL, hLs⟩ := exists_polygon_source_complement Q hQ hinjQ hQsq
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_triangulation_inter L hK hL
  refine ⟨J, hJ, ?_⟩
  rw [hJs, hKs, hLs]
  ext x
  simp only [mem_inter_iff, mem_sdiff, mem_union]
  tauto

end Dehn
