import PoincareConjecture.Proofs.M54.ConnectedSum.Coordinates
import PoincareConjecture.Proofs.M54.Mathlib.VanKampenGeneral

set_option autoImplicit false

open Set Metric

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

noncomputable def inclusionMulEquiv (x : (B.closedBallᶜ : Set A.carrier)) :
    FundamentalGroup (B.closedBallᶜ : Set A.carrier) x ≃* FundamentalGroup A.carrier x.1 :=
  VanKampen.inclusionMulEquivAt B.closedBallᶜ B.chartRegion x
    B.closedBall_closed.isOpen_compl B.chartRegion_open B.complement_union_chart
    B.chart_simplyConnected B.overlap_simplyConnected

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

end PoincareConjecture.SurgeryBallEmbedding
