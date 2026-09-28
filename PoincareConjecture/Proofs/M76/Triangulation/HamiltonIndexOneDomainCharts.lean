import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSurfaceCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.LocalRegionSideIncidence
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLChartRestriction









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)




theorem halfspace_of_regular_closed_frontier_chart {X : Type*} [TopologicalSpace X]
    {R : Set X} (hR : IsClosed R) (hreg : closure (interior R) = R)
    {p : X} (hp : p ∈ frontier R) (H : OpenPartialHomeomorph X V)
    (hpH : p ∈ H.source) (hT : H.target = interior (CoordinateHalfBoxes.box 1))
    (hfront : ∀ x ∈ H.source, x ∈ frontier R ↔ (H x).2 = 0) :
    (∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).2) ∨
      (∀ x ∈ H.source, x ∈ R ↔ (H x).2 ≤ 0) := by
  let P : Set V := H.target ∩ (LinearMap.snd ℝ (ℝ × ℝ) ℝ) ⁻¹' Ioi 0
  let N : Set V := H.target ∩ (LinearMap.snd ℝ (ℝ × ℝ) ℝ) ⁻¹' Iio 0
  have hcv : Convex ℝ H.target := by
    rw [hT, CoordinateHalfBoxes.box_eq_closedBall]
    exact (convex_closedBall (0 : V) 1).interior
  have hP : IsPreconnected (H.symm '' P) :=
    (hcv.inter ((convex_Ioi (0 : ℝ)).linear_preimage
      (LinearMap.snd ℝ (ℝ × ℝ) ℝ))).isPreconnected.image H.symm
        (H.continuousOn_symm.mono inter_subset_left)
  have hN : IsPreconnected (H.symm '' N) :=
    (hcv.inter ((convex_Iio (0 : ℝ)).linear_preimage
      (LinearMap.snd ℝ (ℝ × ℝ) ℝ))).isPreconnected.image H.symm
        (H.continuousOn_symm.mono inter_subset_left)
  have hPmem (x : X) (hx : x ∈ H.source) :
      x ∈ H.symm '' P ↔ 0 < (H x).2 := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [H.right_inv hy.1]
      exact hy.2
    · intro ht
      exact ⟨H x, ⟨H.map_source hx, ht⟩, H.left_inv hx⟩
  have hNmem (x : X) (hx : x ∈ H.source) :
      x ∈ H.symm '' N ↔ (H x).2 < 0 := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [H.right_inv hy.1]
      exact hy.2
    · intro ht
      exact ⟨H x, ⟨H.map_source hx, ht⟩, H.left_inv hx⟩
  have hcover : H.source \ frontier R = (H.symm '' P) ∪ (H.symm '' N) := by
    ext x
    constructor
    · rintro ⟨hx, hxf⟩
      have hne : (H x).2 ≠ 0 := fun heq => hxf ((hfront x hx).mpr heq)
      rcases lt_or_gt_of_ne hne with ht | ht
      · exact Or.inr ((hNmem x hx).mpr ht)
      · exact Or.inl ((hPmem x hx).mpr ht)
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · refine ⟨H.map_target hy.1, ?_⟩
        intro hf
        have heq := (hfront (H.symm y) (H.map_target hy.1)).mp hf
        rw [H.right_inv hy.1] at heq
        exact (ne_of_gt hy.2) heq
      · refine ⟨H.map_target hy.1, ?_⟩
        intro hf
        have heq := (hfront (H.symm y) (H.map_target hy.1)).mp hf
        rw [H.right_inv hy.1] at heq
        exact (ne_of_lt hy.2) heq
  have hzero (x : X) (hx : x ∈ H.source) (ht : (H x).2 = 0) : x ∈ R :=
    hR.frontier_subset ((hfront x hx).mpr ht)
  rcases hR.local_complementary_sides hreg hp H.open_source hpH hP hN hcover with h | h
  · left
    intro x hx
    constructor
    · intro hxR
      by_contra hn
      exact h.2 ((hNmem x hx).mpr (lt_of_not_ge hn)) hxR
    · intro ht
      rcases eq_or_lt_of_le ht with heq | hlt
      · exact hzero x hx heq.symm
      · exact interior_subset (h.1 ((hPmem x hx).mpr hlt))
  · right
    intro x hx
    constructor
    · intro hxR
      by_contra hn
      exact h.2 ((hPmem x hx).mpr (lt_of_not_ge hn)) hxR
    · intro ht
      rcases eq_or_lt_of_le ht with heq | hlt
      · exact hzero x hx heq
      · exact interior_subset (h.1 ((hNmem x hx).mpr hlt))






theorem plDomain_of_regular_closed_local_ball_pairs
    {R : Set V3} (hR : IsClosed R) (hreg : closure (interior R) = R)
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (hKs : K.space = frontier R)
    (hlocal : ∀ x : K.space, ∃ d q : Set V3,
      IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ K.space ∧ (x : V3) ∈ d \ q ∧
        IsOpen ((Subtype.val : K.space → V3) ⁻¹' (d \ q))) :
    PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R := by
  classical
  refine ⟨fun x => ⟨(), mem_univ x⟩, ?_, hR, ?_⟩
  · intro i j
    exact (Homeomorph.refl V3).toOpenPartialHomeomorph.self_transition_mem_piecewiseAffineGroupoid
  · intro x hx
    obtain ⟨H, hxH, hHx, hHt, hHPL, _, hHS⟩ :=
      exists_surface_chart_of_local_ball_pairs (by simp) K hK hlocal (hKs.symm ▸ hx)
    have hfront : ∀ y ∈ H.source, y ∈ frontier R ↔ (H y).2 = 0 := by
      simpa only [hKs] using hHS
    let c : V3 ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq (by simp)
    let B := H.transHomeomorph c.symm.toHomeomorph
    have hBPL : B ∈ piecewiseAffineGroupoid V3 := by
      apply (mem_piecewiseAffineGroupoid_iff_forward B).mpr
      have h := (locallyPiecewiseAffineOn_affine
        c.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ).comp hHPL
      change LocallyPiecewiseAffineOn (fun y => c.symm (H y)) H.source
      simpa only [preimage_univ, inter_univ, Function.comp_def,
        ContinuousLinearEquiv.coe_toContinuousAffineEquiv,
        ContinuousAffineEquiv.coe_toContinuousAffineMap] using h
    let ell : V3 →ᴬ[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp
        c.toContinuousAffineEquiv.toContinuousAffineMap
    have hell (y : V3) : ell (B y) = (H y).2 := by
      change (c (c.symm (H y))).2 = (H y).2
      rw [c.apply_symm_apply]
    have hw : ell.contLinear (c.symm ((0 : ℝ × ℝ), 1)) = 1 := by
      change (c (c.symm ((0 : ℝ × ℝ), 1))).2 = 1
      rw [c.apply_symm_apply]
    have hxB : x ∈ B.source := hxH
    have hzero : ell (B x) = 0 := by rw [hell, hHx]; rfl
    have hcompat (i : Unit) :
        (Homeomorph.refl V3).toOpenPartialHomeomorph.symm.trans B ∈
          piecewiseAffineGroupoid V3 := by
      exact (piecewiseAffineGroupoid V3).trans (piecewiseAffineGroupoid V3).id_mem hBPL
    rcases halfspace_of_regular_closed_frontier_chart hR hreg hx H hxH hHt hfront with h | h
    · refine ⟨ell, c.symm ((0 : ℝ × ℝ), 1), B, hw, hxB, hzero, hcompat, ?_⟩
      intro y hy
      rw [hell]
      exact h y hy
    · refine ⟨-ell, -(c.symm ((0 : ℝ × ℝ), 1)), B, ?_, hxB, ?_, hcompat, ?_⟩
      · change - (ell.contLinear (- (c.symm ((0 : ℝ × ℝ), 1)))) = 1
        rw [map_neg, neg_neg, hw]
      · change -ell (B x) = 0
        rw [hzero, neg_zero]
      · intro y hy
        change y ∈ R ↔ 0 ≤ -ell (B y)
        rw [hell, neg_nonneg]
        exact h y hy

end PoincareConjecture.M76.HamiltonIndexOne
