import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Band.CutContacts

/-!
# Geometry near the lower endpoints of an actual band

The positive-height top and the opposite endpoint cut avoid the base.
The chosen cut is the literal straight segment between its endpoints.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, including Claim 19.40,
pp. 470-471. These project constructions provide actual fitted boundary pieces and
contacts for the regional Gauss--Bonnet arguments.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareMT.Topology.Surface

namespace PoincareMT

section Band

variable {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

/-- A lower endpoint of the actual band lies outside its opposite endpoint cut. Source:
`proof-work/tasks/M64/reviews/2026-09-27-intrinsic-obstacle-bands-review.md`, round_1, check
21. -/
theorem m64Intrinsic_band_endpoint_zero_not_opposite (right : Bool) :
    (B.endpointEdge right).map 0 ∉ (if right then B.leftCut else B.rightCut) := by
  have hother : (if right then B.leftCut else B.rightCut) =
      (B.endpointEdge (!right)).map '' Icc (0 : ℝ) 1 := by
    rw [B.endpointEdge_image]
    cases right <;> rfl
  rw [hother]
  rintro ⟨u, hu, heq⟩
  let e : ℝ := if right then 1 else 0
  let e' : ℝ := if !right then 1 else 0
  have he : e ∈ Icc (0 : ℝ) 1 := by cases right <;> simp [e]
  have he' : e' ∈ Icc (0 : ℝ) 1 := by cases right <;> simp [e']
  rw [B.endpointEdge_map, B.endpointEdge_map] at heq
  change B.coordinates (collarParameterEquiv.symm (e', u * B.height e')) =
    B.coordinates (collarParameterEquiv.symm (e, 0 * B.height e)) at heq
  rw [zero_mul] at heq
  have hs := m64Intrinsic_band_height_mem_source B he
    ⟨le_rfl, (B.height_pos he).le⟩
  have hs' := m64Intrinsic_band_height_mem_source B he'
    ⟨mul_nonneg hu.1 (B.height_pos he').le, by nlinarith [hu.2, B.height_pos he']⟩
  have h := congrArg (fun q => (collarParameterEquiv q).1) (B.coordinates.injOn hs' hs heq)
  simp only [collarParameterEquiv.apply_symm_apply] at h
  cases right <;> norm_num [e, e'] at h

/-- The actual band exposes only its lower arc and chosen cut in a neighborhood of that
cut's lower endpoint. Source:
`proof-work/tasks/M64/reviews/2026-09-27-intrinsic-obstacle-bands-review.md`, round_1, check
21. -/
theorem m64Intrinsic_exists_band_endpoint_neighborhood (right : Bool) :
    ∃ N : Set AnnulusCoordinates, IsOpen N ∧ (B.endpointEdge right).map 0 ∈ N ∧
      N ∩ frontier B.carrier ⊆ B.lowerArc ∪
        (B.endpointEdge right).map '' Icc (0 : ℝ) 1 := by
  let other := if right then B.leftCut else B.rightCut
  have hother : other = (B.endpointEdge (!right)).map '' Icc (0 : ℝ) 1 := by
    rw [B.endpointEdge_image]
    cases right <;> rfl
  have hcompact : IsCompact other := by
    rw [hother]
    exact isCompact_Icc.image_of_continuousOn (B.endpointEdge (!right)).smooth.continuousOn
  have hbaseLower := (m64Intrinsic_band_endpoint_mem_lower_iff B right (by norm_num)).mpr rfl
  refine ⟨(B.polygonalTop ∪ other)ᶜ,
    (B.isCompact_polygonalTop.union hcompact).isClosed.isOpen_compl, ?_, ?_⟩
  · rintro (htop | hother)
    · exact disjoint_left.mp (m64Intrinsic_band_top_disjoint_lower B) htop hbaseLower
    · exact m64Intrinsic_band_endpoint_zero_not_opposite B right hother
  · rintro z ⟨hzN, hzfront⟩
    rw [B.frontier_carrier] at hzfront
    rw [B.endpointEdge_image]
    rcases hzfront with ((hlower | htop) | hleft) | hright
    · exact Or.inl hlower
    · exact False.elim (hzN (Or.inl htop))
    · cases right
      · exact Or.inr hleft
      · exact False.elim (hzN (Or.inr hleft))
    · cases right
      · exact False.elim (hzN (Or.inr hright))
      · exact Or.inr hright

end Band

section LinearBand

variable (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces
    (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
    lo a b ua wa ub wb ra rb)

/-- The left endpoint edge ends at the prescribed physical cut tip. Source:
`proof-work/tasks/M64/reviews/2026-09-27-intrinsic-obstacle-bands-review.md`, round_1, check
21. -/
theorem m64Intrinsic_band_left_endpoint_one :
    (B.endpointEdge false).map 1 = L (a, lo a) + ra • L (ua, wa) := by
  rw [B.endpointEdge_map]
  change B.coordinates (collarParameterEquiv.symm (0, 1 * B.height 0)) = _
  rw [one_mul, B.height_zero]
  exact m64Intrinsic_band_left_parameter L B B.interface.left_parameter_mem

/-- The right endpoint edge ends at the prescribed physical cut tip. Source:
`proof-work/tasks/M64/reviews/2026-09-27-intrinsic-obstacle-bands-review.md`, round_1, check
21. -/
theorem m64Intrinsic_band_right_endpoint_one :
    (B.endpointEdge true).map 1 = L (b, lo b) + rb • L (ub, wb) := by
  rw [B.endpointEdge_map]
  change B.coordinates (collarParameterEquiv.symm (1, 1 * B.height 1)) = _
  rw [one_mul, B.height_one]
  exact m64Intrinsic_band_right_parameter L B B.interface.right_parameter_mem

/-- In linear ambient coordinates, an entire endpoint-edge image is the straight segment
between its literal endpoints. Source:
`proof-work/tasks/M64/reviews/2026-09-27-intrinsic-obstacle-bands-review.md`, round_1, check
21. -/
theorem m64Intrinsic_band_endpoint_image_eq_segment (right : Bool) :
    (B.endpointEdge right).map '' Icc (0 : ℝ) 1 =
      segment ℝ ((B.endpointEdge right).map 0) ((B.endpointEdge right).map 1) := by
  rw [B.endpointEdge_image]
  cases right
  · rw [m64Intrinsic_band_left_endpoint_zero, m64Intrinsic_band_left_endpoint_one]
    exact m64Intrinsic_band_left_cut L B
  · rw [m64Intrinsic_band_right_endpoint_zero, m64Intrinsic_band_right_endpoint_one]
    exact m64Intrinsic_band_right_cut L B

end LinearBand

end PoincareMT
