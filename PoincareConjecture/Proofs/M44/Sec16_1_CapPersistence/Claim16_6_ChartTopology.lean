import PoincareConjecture.Definitions.Ch13.MetricSurgery
import PoincareConjecture.Proofs.M44.Mathlib.SmoothImageInverse
import PoincareConjecture.Proofs.M44.Mathlib.PartialHomeomorphCompact
import PoincareConjecture.Proofs.M36.StandardBalls










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SurgeryCapClose

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}



noncomputable def toPartialDiffeomorph (Q : SurgeryCapClose g₀ S g tip scale eta) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace S.carrier ∞ where
  toFun := Q.map
  invFun := Q.inverse
  source := g₀.metric.ball 0 eta⁻¹
  target := Q.map '' g₀.metric.ball 0 eta⁻¹
  map_source' := fun x hx => mem_image_of_mem Q.map hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Q.left_inverse hx]
    exact hx
  left_inv' := Q.left_inverse
  right_inv' := Q.right_inverse
  open_source := by
    rw [M36.standard_ball_eq_euclidean g₀ (inv_pos.mpr Q.eta_pos)]
    exact Metric.isOpen_ball
  open_target := Poincare.isOpen_image_of_smooth_leftInvOn (by
    rw [M36.standard_ball_eq_euclidean g₀ (inv_pos.mpr Q.eta_pos)]
    exact Metric.isOpen_ball) Q.map_smooth Q.inverse_smooth Q.left_inverse
  contMDiffOn_toFun := Q.map_smooth
  contMDiffOn_invFun := Q.inverse_smooth



theorem closure_image_ball
    (Q : SurgeryCapClose g₀ S g tip scale eta)
    {r : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) :
    closure (Q.map '' g₀.metric.ball 0 r) =
      Q.map '' {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal r} := by
  have hcompact : IsCompact (closure (g₀.metric.ball 0 r)) := by
    rw [M36.standard_closure_ball g₀ hr]
    exact M36.standard_closed_ball_compact g₀ hr.le
  have hsub : closure (g₀.metric.ball 0 r) ⊆ Q.toPartialDiffeomorph.source := by
    rw [M36.standard_closure_ball g₀ hr]
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr Q.eta_pos)).mpr hrEta)
  have h := (Q.toPartialDiffeomorph.toOpenPartialHomeomorph).image_closure_of_compact_buffer
    hcompact hsub
  rw [M36.standard_closure_ball g₀ hr] at h
  exact h.symm



theorem frontier_image_ball
    (Q : SurgeryCapClose g₀ S g tip scale eta)
    {r : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) :
    frontier (Q.map '' g₀.metric.ball 0 r) =
      Q.map '' {x | g₀.metric.edist 0 x = ENNReal.ofReal r} := by
  have hopen : IsOpen (g₀.metric.ball 0 r) := by
    rw [M36.standard_ball_eq_euclidean g₀ hr]
    exact Metric.isOpen_ball
  have hcompact : IsCompact (closure (g₀.metric.ball 0 r)) := by
    rw [M36.standard_closure_ball g₀ hr]
    exact M36.standard_closed_ball_compact g₀ hr.le
  have hsub : closure (g₀.metric.ball 0 r) ⊆ Q.toPartialDiffeomorph.source := by
    rw [M36.standard_closure_ball g₀ hr]
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr Q.eta_pos)).mpr hrEta)
  have h := (Q.toPartialDiffeomorph.toOpenPartialHomeomorph).image_frontier_of_compact_buffer
    hopen hcompact hsub
  rw [M36.standard_frontier_ball g₀ hr] at h
  exact h.symm

end PoincareConjecture.SurgeryCapClose
