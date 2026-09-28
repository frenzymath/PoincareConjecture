import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Geometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.TruncatedCap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem exists_normalization_of_bounded_retained_side (D : SphereSurgeryCoreCap v g B)
    (hg : Continuous g) {a : Real} (ha : 0 < a) (ha1 : a < 1)
    (hbound : ∀ p ∉ (D.chart '' closedBall (0 : E2) 1) ∩
      {p : S2 | a < (inner Real v (g p) - D.center) / D.scale},
        (inner Real v (g p) - D.center) / D.scale ≤ a) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y : E3, (inner Real v y - D.center) / D.scale ≤ (1+a)/2 → F y = y) ∧
      (∀ p ∉ (D.chart '' closedBall (0 : E2) 1) ∩
        {p : S2 | a < (inner Real v (g p) - D.center) / D.scale}, F (g p) = g p) ∧
      (∀ p ∉ (D.chart '' closedBall (0 : E2) 1) ∩
        {p : S2 | a < (inner Real v (g p) - D.center) / D.scale},
          (fun q => F (g q)) =ᶠ[𝓝 p] g) ∧
      range (fun p => F (g p)) =
        (fun p => F (g p)) '' ((D.chart '' closedBall (0 : E2) 1) ∩
          {p : S2 | a < (inner Real v (g p) - D.center) / D.scale})ᶜ ∪
        liftPlaneDiffeomorph D.unit_v (D.center+D.scale*a) D.scale D.scale_ne_zero
          D.planeMap '' boundedCylinderNorthernCap v := by
  obtain ⟨φ, _, _, _, F, _, _, hfix, _, himage⟩ :=
    exists_ambient_truncated_cap_normalization D.unit_v D.center D.scale D.scale_ne_zero
      D.planeMap ha ha1
  refine ⟨F, hfix, ?_, ?_, ?_⟩
  · intro p hp
    exact hfix (g p) ((hbound p hp).trans (by linarith))
  · intro p hp
    have hH : Continuous (fun q => (inner Real v (g q) - D.center) / D.scale) :=
      (((innerSL Real v).continuous.comp hg).sub continuous_const).div_const D.scale
    have hlt : (inner Real v (g p) - D.center) / D.scale < (1+a)/2 :=
      (hbound p hp).trans_lt (by linarith)
    filter_upwards [hH.continuousAt.eventually (gt_mem_nhds hlt)] with q hq
    exact hfix (g q) hq.le
  · change range (F ∘ g) = _
    rw [range_comp, D.range_eq_complement_union_truncated_cap a, image_union, himage]
    rw [← image_comp]
    rfl

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
