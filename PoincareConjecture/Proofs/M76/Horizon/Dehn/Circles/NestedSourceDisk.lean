import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall














set_option autoImplicit false

open Set Metric Geometry

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1






theorem exists_nested_circle_source_disk {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1)
    (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (hnest : closure Q.inside ⊆ P.inside)
    (eb : Q.boundary ℝ ≃ₜ P.boundary ℝ) (heb : eb.IsFinitePL) :
    ∃ (H : closure Q.inside ≃ₜ closure P.inside) (j : V2 → V2),
      H.IsFinitePL ∧ FinitePiecewiseAffineOn j (closure Q.inside) ∧
      (∀ x : closure Q.inside, j x = (H x : V2)) ∧
      Topology.IsEmbedding (fun x : closure Q.inside => j x) ∧
      j '' closure Q.inside = closure P.inside ∧
      (∀ x : Q.boundary ℝ, j x = (eb x : V2)) ∧
      (∀ x ∈ closure Q.inside, ∀ y ∈ D \ P.inside,
        j x = y ↔ ∃ hx : x ∈ Q.boundary ℝ, (eb ⟨x, hx⟩ : V2) = y) ∧
      j '' closure Q.inside ∪ (D \ P.inside) = D ∧
      j '' closure Q.inside ∩ (D \ P.inside) = P.boundary ℝ ∧
      IsFinitePLBallPair V2 (j '' closure Q.inside ∪ (D \ P.inside)) R ∧
      R ⊆ D \ P.inside ∧
      Disjoint (j '' closure Q.inside) R ∧
      Disjoint (closure Q.inside) (D \ P.inside) ∧
      D \ ((closure Q.inside) ∪ (D \ P.inside)) = P.inside \ closure Q.inside := by
  obtain ⟨hdP, hiP, hfP, hsP⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
  obtain ⟨hdQ, _, _, _⟩ := polygon_source_region Q
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ (convex_ball _ _) hQsq
  obtain ⟨H, hH, hHb, hHmem⟩ := hdQ.exists_extension hdP eb heb
  obtain ⟨j, hj, hHj⟩ := hH
  have himage : j '' closure Q.inside = closure P.inside := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hHj ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property
    · intro hy
      refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hHj, H.apply_symm_apply]
  have hboundary (x : Q.boundary ℝ) : j x = (eb x : V2) := by
    have h := congrArg Subtype.val (hHb x)
    rwa [hHj] at h
  have hPclosed : closure P.inside ⊆ D := hsP.trans ball_subset_closedBall
  have hcover : j '' closure Q.inside ∪ (D \ P.inside) = D := by
    rw [himage]
    apply Subset.antisymm (union_subset hPclosed sdiff_subset)
    intro x hx
    by_cases hxi : x ∈ P.inside
    · exact Or.inl (subset_closure hxi)
    · exact Or.inr ⟨hx, hxi⟩
  have hcontact : j '' closure Q.inside ∩ (D \ P.inside) = P.boundary ℝ := by
    rw [himage, ← hfP, frontier, isClosed_closure.closure_eq, hiP]
    ext x
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, hPclosed hx.1, hx.2⟩
  have hrim : R ⊆ D \ P.inside := by
    intro x hx
    refine ⟨sphere_subset_closedBall hx, ?_⟩
    intro hxi
    have hxball := hsP (subset_closure hxi)
    exact (ne_of_lt hxball) hx
  refine ⟨H, j, ⟨j, hj, hHj⟩, hj, fun x => (hHj x).symm, ?_, himage,
    hboundary, ?_, hcover, hcontact, ?_, hrim, ?_, ?_, ?_⟩
  · have hfun : (fun x : closure Q.inside => j x) =
        fun x : closure Q.inside => (H x : V2) := funext fun x => (hHj x).symm
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  · intro x hx y hy
    constructor
    · intro hxy
      have hjb : j x ∈ P.boundary ℝ := hcontact ▸
        (show j x ∈ j '' closure Q.inside ∩ (D \ P.inside) from
          ⟨mem_image_of_mem j hx, hxy.symm ▸ hy⟩)
      have hxb : x ∈ Q.boundary ℝ := (hHmem ⟨x, hx⟩).mpr (by rwa [hHj])
      exact ⟨hxb, (hboundary ⟨x, hxb⟩).symm.trans hxy⟩
    · rintro ⟨hxb, hxy⟩
      exact (hboundary ⟨x, hxb⟩).trans hxy
  · rw [hcover]
    exact isFinitePLBallPair_unit_cube
  · rw [himage]
    exact Set.disjoint_left.mpr fun x hx hy => (ne_of_lt (hsP hx)) hy
  · exact Set.disjoint_left.mpr fun x hx hy => hy.2 (hnest hx)
  · ext x
    constructor
    · rintro ⟨hx, hnot⟩
      have hxi : x ∈ P.inside := by
        by_contra h
        exact hnot (Or.inr ⟨hx, h⟩)
      exact ⟨hxi, fun h => hnot (Or.inl h)⟩
    · rintro ⟨hxi, hxQ⟩
      refine ⟨hPclosed (subset_closure hxi), ?_⟩
      rintro (hx | hx)
      · exact hxQ hx
      · exact hx.2 hxi

end Dehn
