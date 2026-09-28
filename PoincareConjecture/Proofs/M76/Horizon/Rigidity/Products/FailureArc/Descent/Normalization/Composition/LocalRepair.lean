import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Family
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.Construction



set_option autoImplicit false
open Set Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ P2} {j : P2 → t.Carrier} {R Fmark : Set M}

structure MarkedSurfaceExceptionRepair
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (a : D.K.space) (W : Set s.Carrier) where
  motion : I → t.Carrier ≃ₜ t.Carrier
  small : Set t.Carrier
  continuous : Continuous (fun z : I × t.Carrier => motion z.1 z.2)
  inverse_continuous : Continuous (fun z : I × t.Carrier => (motion z.1).symm z.2)
  zero : ∀ x, motion 0 x = x
  piecewiseAffine : ∀ u i j, (t.charts i).symm.trans
    ((motion u).toOpenPartialHomeomorph.trans (t.charts j)) ∈ piecewiseAffineGroupoid V3
  region : ∀ u, (motion u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R
  mark : ∀ u, (motion u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark
  outside : ∀ u, EqOn (motion u) id ((step.projection ∘ step.inclusion) ⁻¹' W)ᶜ
  compact : IsCompact small
  small_window : small ⊆ (step.projection ∘ step.inclusion) ⁻¹' W
  source_fixed : ∀ u, EqOn (motion u) id (D.endpoint '' D.K.space \ small)
  center : D.projected a ∈ (step.projection ∘ step.inclusion) '' small
  crossings : ∀ x y : D.K.space, x ≠ y →
    (step.projection ∘ step.inclusion) (motion 1 (D.endpoint x)) =
      (step.projection ∘ step.inclusion) (motion 1 (D.endpoint y)) →
    (step.projection ∘ step.inclusion) (motion 1 (D.endpoint x)) ∈
      (step.projection ∘ step.inclusion) '' (small ∪ motion 1 '' small) →
    ∃ B : ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
      (motion 1 ∘ D.endpoint) D.K.space (s.projection ⁻¹' R) x y,
      B.chart.source ⊆ W

theorem MarkedSurfacePositionData.nonempty_marked_interior_exception_repair
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hboundary : A₀.space = frontier K₀.space) (hF : Fmark ⊆ frontier R)
    (a b : D.K.space) (hab : a ≠ b) (hpair : D.projected a = D.projected b)
    (haint : D.projected a ∈ interior (s.projection ⁻¹' R))
    {W : Set s.Carrier} (hWopen : IsOpen W) (haW : D.projected a ∈ W)
    (hW : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a}) :
    Nonempty (MarkedSurfaceExceptionRepair D a W) := by
  obtain ⟨N, Small, hSmall, _, hSmallW, hcenter, hfix, hcross⟩ :=
    D.exists_interior_exception_repair hboundary a b hab hpair haint hWopen haW hW
      1 zero_lt_one
  refine ⟨{
    motion := N.ambient
    small := Small
    continuous := N.continuous
    inverse_continuous := N.continuous_inverse
    zero := N.zero
    piecewiseAffine := N.ambient_PL
    region := N.region
    mark := ?_
    outside := ?_
    compact := hSmall
    small_window := subset_union_left.trans hSmallW
    source_fixed := hfix
    center := hcenter
    crossings := hcross }⟩
  · intro u
    have hfixed : EqOn (N.ambient u) id (t.projection ⁻¹' Fmark) := by
      intro x hx
      apply N.frontier_fixed u
      rw [t.frontier_region]
      exact hF hx
    ext x
    constructor
    · intro hx
      have he : N.ambient u x = x := (N.ambient u).injective (hfixed hx)
      exact he ▸ hx
    · intro hx
      change N.ambient u x ∈ t.projection ⁻¹' Fmark
      rw [hfixed hx]
      exact hx
  · intro u
    exact right_branch_motion_fixed_off_window N.window N.chart
      N.support_target (fun _ hz => (N.chart_inside hz).2.2)
      (fun _ hz => (N.chart_inside hz).1) (N.outside u)

end Geometry.OriginalPLTower
