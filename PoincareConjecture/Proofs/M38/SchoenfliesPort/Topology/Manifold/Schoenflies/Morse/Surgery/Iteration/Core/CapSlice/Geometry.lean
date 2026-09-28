import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Collars
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapHeight

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem regular_of_normalized_height_mem_Ioo (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {p : S2} (hp : p ∈ D.chart '' closedBall (0 : E2) 1)
    (ht : (inner Real v (g p) - D.center) / D.scale ∈ Ioo (0 : Real) 1) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0 := by
  apply D.regular_on_open_cylindrical_belt hg hp
  have heq : inner Real v (g p) - (D.center + D.scale / 2) =
      D.scale * ((inner Real v (g p) - D.center) / D.scale - 1/2) := by
    field_simp [D.scale_ne_zero]
    ring
  rw [heq, abs_mul]
  have hh : |(inner Real v (g p) - D.center) / D.scale - 1/2| < (1/2 : Real) :=
    abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  nlinarith [abs_pos.mpr D.scale_ne_zero]

theorem critical_mem_complement_of_truncated_cap
    (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {a : Real} (ha1 : a < 1) {p : S2}
    (hp : p ∉ (D.chart '' closedBall (0 : E2) 1) ∩
      {p : S2 | a < (inner Real v (g p) - D.center) / D.scale})
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p = 0) :
    p ∉ D.chart '' ball (0 : E2) 1 := by
  intro hpD
  have hpclosed := image_mono ball_subset_closedBall hpD
  have hle : (inner Real v (g p) - D.center) / D.scale ≤ a :=
    le_of_not_gt (fun h => hp ⟨hpclosed, h⟩)
  exact D.regular_of_normalized_height_mem_Ioo hg hpclosed
    ⟨D.normalized_height_pos_on_open_disk hpD, hle.trans_lt ha1⟩ hc

theorem image_normalized_superlevel (D : SphereSurgeryCoreCap v g B) (a : Real) :
    g '' ((D.chart '' closedBall (0 : E2) 1) ∩
      {p : S2 | a ≤ (inner Real v (g p) - D.center) / D.scale}) =
        (liftPlaneDiffeomorph D.unit_v D.center D.scale D.scale_ne_zero D.planeMap ''
          boundedCylinderNorthernCap v) ∩
            {y : E3 | a ≤ (inner Real v y - D.center) / D.scale} := by
  change g '' ((D.chart '' closedBall (0 : E2) 1) ∩
    g ⁻¹' {y : E3 | a ≤ (inner Real v y - D.center) / D.scale}) = _
  rw [image_inter_preimage, D.image_closedBall, D.range_eq]
  rfl

theorem range_eq_complement_union_truncated_cap (D : SphereSurgeryCoreCap v g B) (a : Real) :
    range g = g '' ((D.chart '' closedBall (0 : E2) 1) ∩
      {p : S2 | a < (inner Real v (g p) - D.center) / D.scale})ᶜ ∪
        ((liftPlaneDiffeomorph D.unit_v D.center D.scale D.scale_ne_zero D.planeMap ''
          boundedCylinderNorthernCap v) ∩
            {y : E3 | a ≤ (inner Real v y - D.center) / D.scale}) := by
  rw [← D.image_normalized_superlevel a]
  apply Subset.antisymm
  · rintro y ⟨p, rfl⟩
    by_cases hp : p ∈ (D.chart '' closedBall (0 : E2) 1) ∩
        {p : S2 | a < (inner Real v (g p) - D.center) / D.scale}
    · exact Or.inr ⟨p, ⟨hp.1,
        le_of_lt (show a < (inner Real v (g p) - D.center) / D.scale from hp.2)⟩, rfl⟩
    · exact Or.inl ⟨p, hp, rfl⟩
  · rintro y (⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) <;> exact mem_range_self _

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
