import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular.Range
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.TruncatedCap

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}

def modelImageAt (D : SphereSurgeryCoreCap v g B) (c : Real) : Set E3 :=
  liftPlaneDiffeomorph D.unit_v c D.scale D.scale_ne_zero D.planeMap ''
    boundedCylinderNorthernCap v

private theorem height_le_modelImageAt (D : SphereSurgeryCoreCap v g B)
    (hs : D.scale < 0) (c : Real) {y : E3} (hy : y ∈ D.modelImageAt c) :
    inner Real v y ≤ c := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [inner_liftPlaneDiffeomorph]
  have hnonneg := height_nonneg_of_mem_boundedCylinderNorthernCap hz
  nlinarith

theorem exists_normalization_of_two_truncated_caps
    (D E : SphereSurgeryCoreCap v g B)
    (hDE : D.center < E.center) (hDscale : D.scale < 0) (hEscale : 0 < E.scale)
    {α β : Real} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (N : Set E3)
    (hN : ∀ y ∈ N, inner Real v y ∈
      Icc (D.center + D.scale * α) (E.center + E.scale * β)) :
    ∃ P : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y ∈ N, P y = y) ∧
      P '' (D.truncatedImage α ∪ N ∪ E.truncatedImage β) =
        D.modelImageAt (D.center + D.scale * α) ∪ N ∪
          E.modelImageAt (E.center + E.scale * β) := by
  obtain ⟨_, _, _, _, L, _, _, hLfix, _, hLimage⟩ :=
    exists_ambient_truncated_cap_normalization D.unit_v D.center D.scale D.scale_ne_zero
      D.planeMap hα hα1
  obtain ⟨_, _, _, _, U, _, _, hUfix, _, hUimage⟩ :=
    exists_ambient_truncated_cap_normalization E.unit_v E.center E.scale E.scale_ne_zero
      E.planeMap hβ hβ1
  have hLcap : L '' D.truncatedImage α = D.modelImageAt (D.center + D.scale * α) := by
    simpa only [truncatedImage, D.range_eq, modelImageAt, boundedCylinderNorthernCap] using hLimage
  have hUcap : U '' E.truncatedImage β = E.modelImageAt (E.center + E.scale * β) := by
    simpa only [truncatedImage, E.range_eq, modelImageAt, boundedCylinderNorthernCap] using hUimage
  have hlow : D.center + D.scale * α < D.center := by nlinarith
  have hupp : E.center < E.center + E.scale * β := by nlinarith
  have hLhigh (y : E3) (hy : D.center + D.scale * α ≤ inner Real v y) : L y = y := by
    apply hLfix
    have hn : (inner Real v y - D.center) / D.scale ≤ α := by
      apply (div_le_iff_of_neg hDscale).mpr
      linarith
    exact hn.trans (by linarith)
  have hUlow (y : E3) (hy : inner Real v y ≤ E.center + E.scale * β) : U y = y := by
    apply hUfix
    have hn : (inner Real v y - E.center) / E.scale ≤ β := by
      apply (div_le_iff₀ hEscale).mpr
      linarith
    exact hn.trans (by linarith)
  have hLN : L '' N = N := image_congr (fun y hy => hLhigh y (hN y hy).1) |>.trans (image_id _)
  have hUN : U '' N = N := image_congr (fun y hy => hUlow y (hN y hy).2) |>.trans (image_id _)
  have hLE : L '' E.truncatedImage β = E.truncatedImage β := by
    apply (image_congr ?_).trans (image_id _)
    intro y hy
    apply hLhigh
    have hh := (le_div_iff₀ hEscale).mp hy.2
    linarith
  have hUD : U '' D.modelImageAt (D.center + D.scale * α) =
      D.modelImageAt (D.center + D.scale * α) := by
    apply (image_congr ?_).trans (image_id _)
    intro y hy
    apply hUlow
    have hh := height_le_modelImageAt D hDscale _ hy
    linarith
  refine ⟨L.trans U, ?_, ?_⟩
  · intro y hy
    change U (L y) = y
    rw [hLhigh y (hN y hy).1, hUlow y (hN y hy).2]
  · change (U ∘ L) '' _ = _
    simp only [image_comp, image_union, hLcap, hLN, hLE, hUD, hUN, hUcap]

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
