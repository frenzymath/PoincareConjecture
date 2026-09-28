import PoincareConjecture.Proofs.M47.BlowupControlsCylinderDerivative
import PoincareConjecture.Proofs.M47.BlowupControlsPinching
import PoincareConjecture.Proofs.M47.JointSeedReciprocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {G : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c A L : ℝ} {U : Set C.carrier}

theorem normalizedCylinderScalar_le
    (h04 : RicciFlowCurvatureTheory.{u})
    (e : GeneralizedFlowCylinder G C origin scale (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) (hc : c ≤ 0) (hA : 0 ≤ A) (hL : 0 < L)
    (hterminal : normalizedCylinderScalar e x 0 ≤ L)
    (hEstimate : ∀ s (hs : s ∈ Ioo c 0), L < normalizedCylinderScalar e x s →
      let p := e.pointMap s (Ioo_subset_Icc_self hs) x
      M45PointwiseAnalyticEstimate (G.metric p.1) (G.connection p.1) p.2 A)
    (hshort : A * L * (-c) ≤ 1 / 4) :
    ∀ s ∈ Icc c 0, normalizedCylinderScalar e x s ≤ 4 * L / 3 := by
  have hcont : ContinuousOn (normalizedCylinderScalar e x) (Icc c 0) := by
    intro s hs
    exact (normalizedCylinderScalar_hasDerivWithinAt h04 e hx s hs).continuousWithinAt
  apply jointSeed_backward_scalar_comparison hc hA hL hcont hterminal ?_ (by
    simpa only [zero_sub] using hshort)
  intro s hs hhigh
  let p := e.pointMap s (Ioo_subset_Icc_self hs) x
  have h := hEstimate s hs hhigh
  have hd := normalizedCylinderScalar_hasDerivWithinAt h04 e hx s (Ioo_subset_Icc_self hs)
  refine ⟨_, hd.hasDerivAt (Icc_mem_nhds hs.1 hs.2), ?_⟩
  have hvalue : normalizedCylinderScalar e x s = G.scalar p / scale := by
    classical
    simp only [normalizedCylinderScalar, dif_pos (Ioo_subset_Icc_self hs), p]
  rw [hvalue, abs_div, abs_of_pos (pow_pos e.scale_pos 2)]
  calc
    _ ≤ (A * G.scalar p ^ 2) / scale ^ 2 :=
      div_le_div_of_nonneg_right h.2.2 (sq_nonneg scale)
    _ = _ := by rw [div_pow]; ring

theorem normalizedCylinder_curvature_bounds
    (P : M46Predecessors.{u}) (hPinched : generalizedHamiltonIveyPinched G)
    (e : GeneralizedFlowCylinder G C origin scale (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) (hc : c ≤ 0) (hA : 0 ≤ A) (hL : 0 < L)
    (hterminal : normalizedCylinderScalar e x 0 ≤ L)
    (hEstimate : ∀ s (hs : s ∈ Ioo c 0), L < normalizedCylinderScalar e x s →
      let p := e.pointMap s (Ioo_subset_Icc_self hs) x
      M45PointwiseAnalyticEstimate (G.metric p.1) (G.connection p.1) p.2 A)
    (hshort : A * L * (-c) ≤ 1 / 4) {eta : ℝ} (heta : 0 < eta)
    (hScale : blowupPinchingThreshold (4 * L / 3) eta ≤ scale) :
    ∀ s (hs : s ∈ Icc c 0),
      let p := e.pointMap s hs x
      |G.curvatureNorm p| ≤ (13 * max (4 * L / 3) 1) * scale ∧
        (G.connection p.1).negativeCurvaturePart p.2 ≤ eta * scale := by
  have hscalar := normalizedCylinderScalar_le P.m04 e hx hc hA hL hterminal hEstimate hshort
  intro s hs
  let p := e.pointMap s hs x
  have ht : p.1 ∈ G.interval := (G.slice_nonempty_iff p.1).mp ⟨p.2⟩
  have hvalue : G.scalar p / scale ≤ 4 * L / 3 := by
    classical
    simpa only [normalizedCylinderScalar, dif_pos hs, p] using hscalar s hs
  exact generalized_blowup_curvature_bounds P G hPinched ht (by positivity) heta hScale
    ((div_le_iff₀ e.scale_pos).mp hvalue)

end PoincareConjecture.M47
