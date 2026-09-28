import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.WholeCrossings
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Crossings.ProjectedChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchMotionSupport









set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ A} {j : A → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}
  {a b : D.K.space} {W : Set s.Carrier} {ε : ℝ}

theorem PlanarSurfaceBranchMotion.exists_crossed_change_support
    (N : PlanarSurfaceBranchMotion step D.K D.endpoint R a b W ε)
    (hWopen : IsOpen W)
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a}) :
    ∃ Small : Set t.Carrier,
      IsCompact Small ∧ IsCompact (Small ∪ N.ambient 1 '' Small) ∧
      Small ∪ N.ambient 1 '' Small ⊆ (step.projection ∘ step.inclusion) ⁻¹' W ∧
      D.projected a ∈ (step.projection ∘ step.inclusion) '' Small ∧
      (∀ u, EqOn (N.ambient u) id (D.endpoint '' D.K.space \ Small)) ∧
      ∀ x y : D.K.space, x ≠ y →
        (step.projection ∘ step.inclusion) (N.ambient 1 (D.endpoint x)) =
          (step.projection ∘ step.inclusion) (N.ambient 1 (D.endpoint y)) →
        (step.projection ∘ step.inclusion) (N.ambient 1 (D.endpoint x)) ∈
          (step.projection ∘ step.inclusion) '' (Small ∪ N.ambient 1 '' Small) →
        ∃ B : ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
          (N.ambient 1 ∘ D.endpoint) D.K.space (s.projection ⁻¹' R) x y,
          B.chart.source ⊆ W := by
  obtain ⟨Small, hSmall, hEnd, hinner, hSmallW, hcenter, hfix⟩ := N.compact_change_support
  refine ⟨Small, hSmall, hEnd, hSmallW, hcenter, hfix, ?_⟩
  intro x y hxy hpair hpointSmall
  let p := step.projection ∘ step.inclusion
  let d := N.ambient 1 ∘ D.endpoint
  have hne : d x ≠ d y := fun h ↦
    hxy ((D.states D.length).embedding.injective ((N.ambient 1).injective h))
  obtain ⟨v, hv, hvp⟩ := hpointSmall
  obtain ⟨z, hzJ, hzs⟩ := hinner hv
  have hzQt := N.support_target (interior_subset hzJ)
  have hzWr : N.chart.symm z ∈ N.window.right.target :=
    N.window.right_target.symm.subset ((N.chart_inside (N.chart.map_target hzQt)).2.2)
  have hpoint : p (d x) = N.chart.symm z := by
    change p v = p (d x) at hvp
    rw [← hvp, ← hzs]
    change p (N.window.right.symm (N.chart.symm z)) = N.chart.symm z
    exact (congrFun N.window.right_eq _).symm.trans (N.window.right.right_inv hzWr)
  have hxQ : p (d x) ∈ N.chart.source := hpoint.symm ▸ N.chart.map_target hzQt
  obtain ⟨hleftPoint, hrightPoint⟩ := twoBranchWindow_double_images N.window
    (mem_image_of_mem d x.property) (mem_image_of_mem d y.property)
    hne hpair ((N.chart_inside hxQ).2.2)
  have hzvalue : N.chart (p (d x)) = z := by rw [hpoint, N.chart.right_inv hzQt]
  have hz0 : (N.coordinates z).2 = 0 := by
    have hl : p (d x) ∈ p '' (D.endpoint '' D.K.space ∩ N.window.left.source) := by
      rw [← N.moved_left_image 1]
      exact hleftPoint
    have h := (N.left_plane _ hxQ).mp hl
    rwa [hzvalue] at h
  have hzK : z ∈ N.movedBranch.space := by
    apply N.moved_right_image.subset
    obtain ⟨v, ⟨hvD, hvR⟩, hvp⟩ := hrightPoint
    refine ⟨⟨v, ⟨hvD, hvR, ?_⟩, ?_⟩, interior_subset hzJ⟩
    · change N.window.right v ∈ N.chart.source
      rw [congrFun N.window.right_eq v, hvp]
      exact hxQ
    · change N.chart (N.window.right v) = z
      rw [congrFun N.window.right_eq v, hvp]
      exact hzvalue
  obtain ⟨T, hzT, _, hTW, hTPL, _, hleft, hright⟩ := N.exists_whole_crossing
    hW hzK hzJ hz0 W hWopen (N.chart_inside (N.chart.map_target hzQt)).1
  have hTin : T.source ⊆ interior (s.projection ⁻¹' R) := fun _ hv ↦ (hTW hv).2.2
  obtain ⟨B, hBs⟩ := ProjectedSourceCrossing.exists_of_linear_coordinates
    s.charts p d D.K.space (s.projection ⁻¹' R) x y N.window T
    (N.coordinates.trans crossingCoordinatesRightLast) hne hpair (hpoint.symm ▸ hzT)
    (fun _ hz ↦ (N.chart_inside (hTW hz).2.1).2.2) hTPL
    (fun v hv ↦ (hleft v hv).trans
      ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩)
    (fun v hv ↦ (hright v hv).trans
      ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩)
    (Or.inl hTin)
  exact ⟨B, fun v hv ↦ (hTW (hBs ▸ hv)).1⟩

end Geometry.OriginalPLTower

