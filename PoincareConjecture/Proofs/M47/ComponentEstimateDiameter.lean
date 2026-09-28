import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter
import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

theorem component_cylinder_image_diameter_lt
    {F : SurgeryFlowData.{u}} {origin C Q : ℝ} {I : Set ℝ}
    (N : SingularCComponent (F.metric origin) (F.connection origin) (2 * C))
    {x : (F.slice origin).carrier} (hx : x ∈ N.carrier)
    (hxQ : (F.connection origin).scalarCurvature x = Q)
    (U : TopologicalSpace.Opens (F.slice origin).carrier)
    (hU : (U : Set (F.slice origin).carrier) = N.carrier)
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 I U)
    (s : ℝ) (hs : s ∈ I)
    (hquadratic : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 3) y,
      e.pullbackInner s hs y v v ≤ 2 * (F.metric origin).inner y v v) :
    intrinsicDiameter (F.metric (origin + s / 1)) (e.forward s hs '' (U : Set _)) <
      ENNReal.ofReal (4 * C / Real.sqrt Q) := by
  have hQ : 0 < Q := hxQ ▸ component_scalar_pos N hx
  have hbound : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 3) y,
      (F.metric (origin + s / 1)).tangentNorm (e.forward s hs y)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) y v) ≤
          2 * (F.metric origin).tangentNorm y v := by
    intro y hy v
    have hquad := hquadratic y hy v
    simp only [SurgeryFlowCylinder.pullbackInner, one_mul] at hquad
    have hnonneg : 0 ≤ (F.metric origin).inner y v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact ((F.metric origin).pos y v hv).le
    change Real.sqrt _ ≤ 2 * Real.sqrt _
    calc
      _ ≤ Real.sqrt (4 * (F.metric origin).inner y v v) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hmap := (F.metric origin).intrinsicDiameter_image_le_mul_of_isOpen
    (F.metric (origin + s / 1)) (e.forward s hs) U.isOpen
    ((e.forward_smooth s hs).of_le (by simp)) (by norm_num : (0 : ℝ) < 2) hbound
  have hdiam := component_diameter_lt N hx
  rw [← hU] at hdiam
  rw [hxQ] at hdiam
  have hradius : (2 * C) * Q ^ (-1 / 2 : ℝ) = 2 * C / Real.sqrt Q := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg,
      ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    exact hQ.le
  rw [hradius] at hdiam
  have hstrict := ENNReal.mul_lt_mul_right
    (show (ENNReal.ofReal 2) ≠ 0 by norm_num) ENNReal.ofReal_ne_top hdiam
  have hvalue : ENNReal.ofReal 2 * ENNReal.ofReal (2 * C / Real.sqrt Q) =
      ENNReal.ofReal (4 * C / Real.sqrt Q) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  exact hmap.trans_lt (hstrict.trans_eq hvalue)

end PoincareConjecture.M47
