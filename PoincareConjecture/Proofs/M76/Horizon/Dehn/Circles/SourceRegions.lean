import PoincareConjecture.Proofs.M76.Mathlib.DisjointPolygonNesting
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionLinearImage
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set

namespace Polygon

theorem closed_inside_nested_or_disjoint {m n : ℕ}
    (P : Polygon (ℝ × ℝ) (m + 3)) (Q : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hdisj : Disjoint (P.boundary ℝ) (Q.boundary ℝ)) :
    closure P.inside ⊆ Q.inside ∨ closure Q.inside ⊆ P.inside ∨
      Disjoint (closure P.inside) (closure Q.inside) := by
  rcases P.boundary_subset_inside_or_outside_of_disjoint Q hP hinjP hQ hinjQ hdisj
      with hQP | hQP
  · exact Or.inr (Or.inl
      (P.closure_inside_subset_inside_of_boundary_subset_inside Q hP hinjP hQ hinjQ hQP))
  rcases Q.boundary_subset_inside_or_outside_of_disjoint P hQ hinjQ hP hinjP hdisj.symm
      with hPQ | hPQ
  · exact Or.inl
      (Q.closure_inside_subset_inside_of_boundary_subset_inside P hQ hinjQ hP hinjP hPQ)
  have hsplit : P.inside ⊆ Q.inside ∨ P.inside ⊆ Q.outside := by
    apply (P.isConnected_inside hP hinjP).isPreconnected.subset_or_subset
      (Q.isOpen_inside hQ hinjQ) (Q.isOpen_outside hQ hinjQ) Q.disjoint_inside_outside
    rw [← Q.compl_boundary_eq_inside_union_outside]
    intro x hx hxb
    exact Set.disjoint_left.mp P.disjoint_inside_outside hx (hQP hxb)
  have hinside : Disjoint P.inside Q.inside := by
    rcases hsplit with hsub | hsub
    · obtain ⟨x, hxb⟩ := (P.isConnected_boundary hP hinjP).nonempty
      have hxcl : x ∈ closure P.inside := by
        rw [← P.frontier_inside hP hinjP] at hxb
        exact frontier_subset_closure hxb
      have hx := closure_mono hsub hxcl
      rw [Q.closure_inside hQ hinjQ] at hx
      exact (hx (hPQ hxb)).elim
    · exact Set.disjoint_left.mpr fun x hx hy =>
        Set.disjoint_left.mp Q.disjoint_inside_outside hy (hsub hx)
  apply Or.inr ∘ Or.inr
  rw [Set.disjoint_iff_inter_eq_empty,
    P.closure_inside_inter_eq_boundary_inter Q hP hinjP hQ hinjQ hinside]
  exact Set.disjoint_iff_inter_eq_empty.mp hdisj

end Polygon

namespace Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem polygon_source_region {n : ℕ} (P : Polygon E (n + 3))
    (e : E ≃L[ℝ] (ℝ × ℝ))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {U : Set E} (hU : Convex ℝ U) (hPU : P.boundary ℝ ⊆ U) :
    IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) ∧
      interior (closure P.inside) = P.inside ∧
      frontier (closure P.inside) = P.boundary ℝ ∧
      closure P.inside ⊆ U := by
  let Q := P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap
  have hQ := P.affineImage_of_leftInvOn hP hinj
    e.toLinearEquiv.toAffineEquiv.toAffineMap
    e.symm.toLinearEquiv.toAffineEquiv.toAffineMap (fun _ _ => e.symm_apply_apply _)
  have hcl : closure Q.inside = e '' closure P.inside := P.closure_inside_linearImage e
  have hb : Q.boundary ℝ = e '' P.boundary ℝ := P.affineImage_boundary _
  have hi : Q.inside = e '' P.inside := P.inside_linearImage e
  have hd := (Q.isFinitePLBallPair_closed_inside hQ.2.1 hQ.1).affine_image
    e.symm.toContinuousLinearMap.toContinuousAffineMap e.symm.injective.injOn
  have hball : IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
    simpa only [hcl, hb, image_image, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, image_id'] using hd
  refine ⟨hball, ?_, ?_, ?_⟩
  · apply e.injective.image_injective
    have hei : e '' interior (closure P.inside) = interior (e '' closure P.inside) :=
      e.toHomeomorph.image_interior _
    rw [hei, ← hcl, ← hi]
    exact Q.interior_closure_inside hQ.2.1 hQ.1
  · apply e.injective.image_injective
    have hef : e '' frontier (closure P.inside) = frontier (e '' closure P.inside) :=
      e.toHomeomorph.image_frontier _
    rw [hef, ← hcl, ← hb]
    exact Q.frontier_closure_inside hQ.2.1 hQ.1
  · have hcontained : closure Q.inside ⊆ e '' U :=
      Q.closure_inside_subset_convex hQ.2.1 hQ.1
        (hU.linear_image e.toLinearMap) (by
          rintro _ ⟨i, rfl⟩
          exact ⟨P i, hPU (P.vertex_mem_boundary i), rfl⟩)
    intro x hx
    exact e.injective.mem_set_image.mp (hcontained (hcl ▸ mem_image_of_mem e hx))

theorem interior_polygon_source_regions {m n : ℕ}
    (P : Polygon (Fin 2 → ℝ) (m + 3)) (Q : Polygon (Fin 2 → ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hdisj : Disjoint (P.boundary ℝ) (Q.boundary ℝ))
    (hPsq : P.boundary ℝ ⊆ Metric.ball 0 1)
    (hQsq : Q.boundary ℝ ⊆ Metric.ball 0 1) :
    IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) (closure Q.inside) (Q.boundary ℝ) ∧
      interior (closure P.inside) = P.inside ∧
      interior (closure Q.inside) = Q.inside ∧
      frontier (closure P.inside) = P.boundary ℝ ∧
      frontier (closure Q.inside) = Q.boundary ℝ ∧
      closure P.inside ⊆ Metric.ball 0 1 ∧
      closure Q.inside ⊆ Metric.ball 0 1 ∧
      (closure P.inside ⊆ interior (closure Q.inside) ∨
        closure Q.inside ⊆ interior (closure P.inside) ∨
        Disjoint (closure P.inside) (closure Q.inside)) := by
  let e := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  obtain ⟨hdP, hiP, hfP, hsP⟩ := polygon_source_region P e hP hinjP (convex_ball _ _) hPsq
  obtain ⟨hdQ, hiQ, hfQ, hsQ⟩ := polygon_source_region Q e hQ hinjQ (convex_ball _ _) hQsq
  refine ⟨hdP, hdQ, hiP, hiQ, hfP, hfQ, hsP, hsQ, ?_⟩
  let P' := P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap
  let Q' := Q.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap
  have hp := P.affineImage_of_leftInvOn hP hinjP
    e.toLinearEquiv.toAffineEquiv.toAffineMap
    e.symm.toLinearEquiv.toAffineEquiv.toAffineMap (fun _ _ => e.symm_apply_apply _)
  have hq := Q.affineImage_of_leftInvOn hQ hinjQ
    e.toLinearEquiv.toAffineEquiv.toAffineMap
    e.symm.toLinearEquiv.toAffineEquiv.toAffineMap (fun _ _ => e.symm_apply_apply _)
  have hd : Disjoint (P'.boundary ℝ) (Q'.boundary ℝ) := by
    change Disjoint ((P.affineImage _).boundary ℝ) ((Q.affineImage _).boundary ℝ)
    rw [P.affineImage_boundary, Q.affineImage_boundary]
    exact hdisj.image e.injective.injOn (subset_univ _) (subset_univ _)
  have halt := P'.closed_inside_nested_or_disjoint Q' hp.2.1 hp.1 hq.2.1 hq.1 hd
  change closure (P.affineImage _).inside ⊆ (Q.affineImage _).inside ∨
    closure (Q.affineImage _).inside ⊆ (P.affineImage _).inside ∨ _ at halt
  rw [P.closure_inside_linearImage e, Q.closure_inside_linearImage e,
    P.inside_linearImage e, Q.inside_linearImage e] at halt
  rw [hiP, hiQ]
  rcases halt with h | h | h
  · exact Or.inl (fun x hx => e.injective.mem_set_image.mp (h (mem_image_of_mem e hx)))
  · exact Or.inr (Or.inl
      (fun x hx => e.injective.mem_set_image.mp (h (mem_image_of_mem e hx))))
  · exact Or.inr (Or.inr (Set.disjoint_left.mpr fun x hx hy =>
      Set.disjoint_left.mp h (mem_image_of_mem e hx) (mem_image_of_mem e hy)))

end Dehn
