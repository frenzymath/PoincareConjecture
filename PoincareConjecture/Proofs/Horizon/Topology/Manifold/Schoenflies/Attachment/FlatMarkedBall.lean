import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.BallBoundaryChart
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)


def unitBallMarkedCone (v : E3) (r : Real) : Set E3 :=
  {y | 0 < inner Real v y ∧
    ‖(inner Real v y)⁻¹ • (Hemisphere.Plane v).orthogonalProjectionOnto y‖ < r}

theorem isOpen_unitBallMarkedCone (v : E3) (r : Real) : IsOpen (unitBallMarkedCone v r) := by
  have hU : IsOpen {y : E3 | 0 < inner Real v y} :=
    isOpen_lt continuous_const (innerSL Real v).continuous
  have hc : ContinuousOn (fun y : E3 =>
      ‖(inner Real v y)⁻¹ • (Hemisphere.Plane v).orthogonalProjectionOnto y‖)
      {y : E3 | 0 < inner Real v y} :=
    (((innerSL Real v).continuous.continuousOn.inv₀ (fun _ hy => ne_of_gt hy)).smul
      (Hemisphere.Plane v).orthogonalProjectionOnto.continuous.continuousOn).norm
  exact hc.isOpen_inter_preimage hU isOpen_Iio

private theorem mem_unitBallBoundary_graphImage_iff {v : E3} (hv : ‖v‖ = 1)
    (b : Hemisphere.Plane v → Real) (y : unitBallBoundaryHalfSpace v) :
    (y : E3) ∈ (fun z : Hemisphere.Plane v × Real =>
      Real.exp z.2 • (Hemisphere.toSphere hv z.1 : E3)) '' {z | z.2 ≤ b z.1} ↔
      (unitBallBoundaryChart hv y).2 ≤ b (unitBallBoundaryChart hv y).1 := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hsub : (unitBallBoundaryChart hv).symm z = y := Subtype.ext hzy
    have heq : z = unitBallBoundaryChart hv y := by
      simpa using congrArg (unitBallBoundaryChart hv) hsub
    simpa only [heq, mem_ofPred_eq] using hz
  · intro hy
    exact ⟨unitBallBoundaryChart hv y, hy,
      congrArg Subtype.val ((unitBallBoundaryChart hv).symm_apply_apply y)⟩

private theorem unitBallBoundary_height_le_log_iff {v : E3} (hv : ‖v‖ = 1)
    (y : unitBallBoundaryHalfSpace v) :
    (unitBallBoundaryChart hv y).2 ≤
        Real.log ‖((unitBallBoundaryChart hv y).1 : E3) + v‖ ↔
      inner Real v (y : E3) ≤ 1 := by
  let z := unitBallBoundaryChart hv y
  have hn : 0 < ‖(z.1 : E3) + v‖ :=
    norm_pos_iff.mpr (Hemisphere.add_center_ne_zero hv z.1)
  have hrepr : ((unitBallBoundaryChart hv).symm z : E3) = (y : E3) :=
    congrArg Subtype.val ((unitBallBoundaryChart hv).symm_apply_apply y)
  have hheight : inner Real v (y : E3) = Real.exp z.2 / ‖(z.1 : E3) + v‖ := by
    rw [← hrepr, unitBallBoundaryChart_symm_apply, inner_smul_right,
      Hemisphere.inner_toSphere, div_eq_mul_inv]
  change z.2 ≤ Real.log ‖(z.1 : E3) + v‖ ↔ _
  rw [Real.le_log_iff_exp_le hn, hheight, div_le_one hn]

private theorem unitBall_graphImage_inter_cone {v : E3} (hv : ‖v‖ = 1)
    (r : Real) (b : Hemisphere.Plane v → Real)
    (hb : ∀ x, ‖x‖ < r → b x = Real.log ‖(x : E3) + v‖) :
    ((closedBall (0 : E3) 1 \ unitBallBoundaryHalfSpace v) ∪
      (fun z : Hemisphere.Plane v × Real =>
        Real.exp z.2 • (Hemisphere.toSphere hv z.1 : E3)) '' {z | z.2 ≤ b z.1}) ∩
        unitBallMarkedCone v r =
      {y | y ∈ unitBallMarkedCone v r ∧ inner Real v y ≤ 1} := by
  ext y
  by_cases hy : y ∈ unitBallMarkedCone v r
  · let q : unitBallBoundaryHalfSpace v := ⟨y, hy.1⟩
    have hcoord : ‖(unitBallBoundaryChart hv q).1‖ < r := hy.2
    have hmem : y ∈ (fun z : Hemisphere.Plane v × Real =>
        Real.exp z.2 • (Hemisphere.toSphere hv z.1 : E3)) '' {z | z.2 ≤ b z.1} ↔
        inner Real v y ≤ 1 := by
      rw [show y = (q : E3) from rfl,
        mem_unitBallBoundary_graphImage_iff hv b q,
        hb _ hcoord, unitBallBoundary_height_le_log_iff hv q]
    simp only [mem_inter_iff, mem_union, mem_sdiff, mem_ofPred_eq, hy, and_true, true_and]
    have hyU : y ∈ (unitBallBoundaryHalfSpace v : Set E3) := hy.1
    simp only [hyU, not_true_eq_false, and_false, false_or, hmem]
  · simp only [mem_inter_iff, mem_ofPred_eq, hy, and_false, false_and]




theorem exists_flat_marked_unitBall {v : E3} (hv : ‖v‖ = 1)
    {r : Real} (hr : 0 < r) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ unitBallBoundaryHalfSpace v ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧
        (∀ x : Hemisphere.Plane v, ‖x‖ ≤ r →
          F (Hemisphere.toSphere hv x) = (x : E3) + v) ∧
        (F '' closedBall (0 : E3) 1) ∩ unitBallMarkedCone v r =
          {y | y ∈ unitBallMarkedCone v r ∧ inner Real v y ≤ 1} := by
  let χ : ContDiffBump (0 : Hemisphere.Plane v) := ⟨r, r + 1, hr, lt_add_one r⟩
  let b : Hemisphere.Plane v → Real := fun x => χ x * Real.log ‖(x : E3) + v‖
  have hadd : ContDiff Real ∞ (fun x : Hemisphere.Plane v => (x : E3) + v) :=
    (Hemisphere.Plane v).subtypeL.contDiff.add contDiff_const
  have hlog : ContDiff Real ∞ (fun x : Hemisphere.Plane v => Real.log ‖(x : E3) + v‖) :=
    (hadd.norm Real (Hemisphere.add_center_ne_zero hv)).log
      (fun x => norm_ne_zero_iff.mpr (Hemisphere.add_center_ne_zero hv x))
  have hb : ContDiff Real ∞ b := χ.contDiff.mul hlog
  have hbc : HasCompactSupport b := χ.hasCompactSupport.mul_right
  have hbEq (x : Hemisphere.Plane v) (hx : ‖x‖ ≤ r) : b x = Real.log ‖(x : E3) + v‖ := by
    have hxb : x ∈ closedBall (0 : Hemisphere.Plane v) r := by simpa using hx
    simp only [b, χ.one_of_mem_closedBall hxb, one_mul]
  obtain ⟨K, hK, hKU, F, hfix, hzero, hside⟩ :=
    exists_unitBall_boundary_graph_push hv b hb hbc
  refine ⟨K, hK, hKU, F, hfix, ?_, ?_⟩
  · intro x hx
    rw [hzero, hbEq x hx, Real.exp_log
      (norm_pos_iff.mpr (Hemisphere.add_center_ne_zero hv x))]
    simp only [Hemisphere.toSphere, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr (Hemisphere.add_center_ne_zero hv x)), one_smul]
  · rw [hside]
    exact unitBall_graphImage_inter_cone hv r b (fun x hx => hbEq x hx.le)

end Poincare.Manifold.Schoenflies
