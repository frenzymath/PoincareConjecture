import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarBoundaryContainment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionSides
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_common_cap_exterior_filling
    (hP : PlanarSchoenfliesService)
    (B : BallNeighborhoodChart E2 E2)
    (c : UnitCircle → E2) (hc : IsPlanarEmbedding c)
    (K O T Delta : Set E2)
    (hK : IsPreconnected K)
    (hOutside : ∃ x ∈ K, x ∉ B.closedRegion)
    (hCurve : range c ⊆ B.closedRegion)
    (hCurveK : Disjoint (range c) K)
    (hOther : O ⊆ B.closedRegionᶜ)
    (hTail : T ⊆ B.boundary)
    (hMeet : range c ∩ T ⊆ Delta) :
    ∃ D : BallNeighborhoodChart E2 E2,
      D.boundary = range c ∧ D.closedRegion ⊆ B.closedRegion ∧
      D.closedRegion ∩ (K ∪ O ∪ T) ⊆ Delta ∧
      let W := D.closedRegionᶜ
      IsOpen W ∧ IsConnected W ∧ ¬ Bornology.IsBounded W ∧
      Disjoint W (range c) ∧ (K ∪ O ∪ T) \ Delta ⊆ W := by
  classical
  obtain ⟨P⟩ := hP.1 c hc
  let D : BallNeighborhoodChart E2 E2 := P.ballNeighborhoodChart
  have hDb : D.boundary = range c := P.discChart_image_sphere
  have hsub : D.closedRegion ⊆ B.closedRegion :=
    saddle_planar_closedRegion_subset_of_boundary_subset B D (by rwa [hDb])
  have hinside : D.inside ⊆ B.inside := by
    rw [← D.interior_closedRegion, ← B.interior_closedRegion]
    exact interior_mono hsub
  have hKD : Disjoint K D.boundary := by
    rw [hDb]
    exact hCurveK.symm
  have hKout : K ⊆ D.closedRegionᶜ := by
    rcases D.preconnected_subset_inside_or_outside hK hKD with hi | ho
    · obtain ⟨x, hx, hxB⟩ := hOutside
      apply False.elim
      apply hxB
      rw [← B.inside_union_boundary]
      exact Or.inl (hinside (hi hx))
    · exact ho
  have hprotect : D.closedRegion ∩ (K ∪ O ∪ T) ⊆ Delta := by
    rintro x ⟨hx, (hxK | hxO) | hxT⟩
    · exact False.elim (hKout hxK hx)
    · exact False.elim (hOther hxO (hsub hx))
    · have hxB := hTail hxT
      have hxD : x ∈ D.boundary := by
        rw [← D.inside_union_boundary] at hx
        rcases hx with hi | hb
        · exact False.elim (disjoint_left.mp B.inside_disjoint_boundary (hinside hi) hxB)
        · exact hb
      exact hMeet ⟨hDb ▸ hxD, hxT⟩
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have hconn : IsConnected D.closedRegionᶜ := by
    simpa only [D.inside_union_boundary, compl_eq_univ_sdiff] using D.outside_connected hdim
  have hunbounded : ¬ Bornology.IsBounded D.closedRegionᶜ := by
    intro hb
    apply NormedSpace.unbounded_univ ℝ E2
    have hh := D.closedRegion_compact.isBounded.union hb
    simpa only [union_compl_self] using hh
  refine ⟨D, hDb, hsub, hprotect, D.closedRegion_compact.isClosed.isOpen_compl,
    hconn, hunbounded, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro y hy hc'
    apply hy
    rw [← D.inside_union_boundary, hDb]
    exact Or.inr hc'
  · rintro y ⟨hy, hyDelta⟩ hyD
    exact hyDelta (hprotect ⟨hyD, hy⟩)

end PoincareConjecture.M25.Topology3D
