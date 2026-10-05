import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Coordinates
import PoincareLib.AlgebraicTopology.FundamentalGroup.VanKampen.General

/-! Adapted from Mapher `PoincareMT/Proofs/M54/ConnectedSum/RemoveBall.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Filling the ball in a punctured summand

The inclusion of the complement of the removed closed ball induces a
fundamental-group isomorphism. Every original basepoint can be transported
to that complement, including when it lies inside the ball. Sources:
Morgan--Tian Proposition 15.3, pp. 357-358; Hatcher Proposition 1.26(b), p. 50.
-/

set_option autoImplicit false

open Set Metric

universe u

namespace PoincareMT.SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

/-- Filling the removed ball preserves the group at each point of its
complement (Hatcher Proposition 1.26(b), p. 50). -/
noncomputable def inclusionMulEquiv (x : (B.closedBallᶜ : Set A.carrier)) :
    FundamentalGroup (B.closedBallᶜ : Set A.carrier) x ≃* FundamentalGroup A.carrier x.1 :=
  VanKampen.inclusionMulEquivAt B.closedBallᶜ B.chartRegion x
    B.closedBall_closed.isOpen_compl B.chartRegion_open B.complement_union_chart
    B.chart_simplyConnected B.overlap_simplyConnected

/-- Every basepoint of the original summand has its group represented in
the punctured summand, without a connectedness assumption on the manifold.
Sources: MT Proposition 15.3; Hatcher Proposition 1.26(b), p. 50. -/
theorem exists_complement_group_equiv (x : A.carrier) :
    ∃ y : (B.closedBallᶜ : Set A.carrier),
      Nonempty (FundamentalGroup (B.closedBallᶜ : Set A.carrier) y ≃*
        FundamentalGroup A.carrier x) := by
  classical
  by_cases hx : x ∈ B.closedBallᶜ
  · exact ⟨⟨x, hx⟩, ⟨B.inclusionMulEquiv ⟨x, hx⟩⟩⟩
  · have hxB : x ∈ B.closedBall := not_not.mp hx
    obtain ⟨v, hv, rfl⟩ := hxB
    let : SimplyConnectedSpace UnitTwoSphere := SurgeryCoordinates.sphere_simplyConnected
    let z : UnitTwoSphere := Classical.choice inferInstance
    have hr : (3 / 2 : ℝ) ∈ Ioo (1 : ℝ) 2 := by constructor <;> norm_num
    have hw : B.map ((3 / 2 : ℝ) • z.1) ∈ B.closedBallᶜ := B.radial_mem_complement z hr
    have hv2 : v ∈ ball (0 : StandardCapSpace) 2 := closedBall_subset_ball (by norm_num) hv
    have hw2 : (3 / 2 : ℝ) • z.1 ∈ ball (0 : StandardCapSpace) 2 := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp z.2, mul_one]
      norm_num
    let : ContractibleSpace (ball (0 : StandardCapSpace) 2) :=
      (convex_ball (0 : StandardCapSpace) 2).contractibleSpace ⟨v, hv2⟩
    let p := (PathConnectedSpace.somePath (⟨(3 / 2 : ℝ) • z.1, hw2⟩ : ball _ 2)
      ⟨v, hv2⟩).map B.map_smooth.continuousOn.domRestrict
    exact ⟨⟨B.map ((3 / 2 : ℝ) • z.1), hw⟩,
      ⟨(B.inclusionMulEquiv _).trans (FundamentalGroup.fundamentalGroupMulEquivOfPath p)⟩⟩

end PoincareMT.SurgeryBallEmbedding
