import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Contacts.Charts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.InnerSupport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.WholeCrossings
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
  {a b : PLAnnularStrip.squareAnnulus 8 1} {W : Set s.Carrier} {ε : ℝ}

theorem PlanarAnnulusBoundaryMotion.exists_crossed_change_support
    (N : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
    (hAnn : D.K.space = PLAnnularStrip.squareAnnulus 8 1)
    (hRim : A₀.space = Set.ofPred (fun z : A => PLAnnularStrip.depth 8 z = -1 ∨
      PLAnnularStrip.depth 8 z = 1))
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
  classical
  obtain ⟨B, K, _hB, _hK, _hKB, hBs, _hKs, hKzero, hcross⟩ :=
    D.exists_annulus_boundary_crossed_charts hAnn hRim N hW
  obtain ⟨Small, hSmall, hEnd, hinner, _hSmallW, hfix, _hout, hcenter⟩ :=
    N.exists_inner_change_support
  let p := step.projection ∘ step.inclusion
  let d := N.ambient 1 ∘ D.endpoint
  have hSmallW : Small ∪ N.ambient 1 '' Small ⊆ p ⁻¹' W :=
    hinner.trans ((image_mono interior_subset).trans
      (right_branch_chart_support_subset N.window N.chart N.support_target
        (fun _ hz ↦ (N.chart_inside hz).2) (fun _ hz ↦ (N.chart_inside hz).1)))
  have hleftimage : d '' PLAnnularStrip.squareAnnulus 8 1 ∩ N.window.left.source =
      D.endpoint '' PLAnnularStrip.squareAnnulus 8 1 ∩ N.window.left.source := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx⟩
      have he : N.ambient 1 (D.endpoint y) = x := hyx
      have hold : D.endpoint y = x :=
        (N.ambient 1).injective (he.trans (N.left_fixed 1 hx).symm)
      exact ⟨⟨y, hy, hold⟩, hx⟩
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨⟨y, hy, N.left_fixed 1 hx⟩, hx⟩
  have hHK : N.branchComplex.AffineOnFaces (N.motion.map 1) :=
    fun face hf ↦ N.endpoint_affine face (N.branch_le hf)
  let B' := hHK.embeddedImage (N.motion.map 1).injective.injOn
  have hB's : B'.space = B.space := by
    rw [hHK.embeddedImage_space, N.branch_space, hBs, N.source_image 1]
  refine ⟨Small, hSmall, hEnd, hSmallW, hcenter, ?_, ?_⟩
  · simpa only [hAnn] using hfix
  intro x y hxy hpair hpointSmall
  have hne : d x ≠ d y := fun h ↦
    hxy ((D.states D.length).embedding.injective ((N.ambient 1).injective h))
  obtain ⟨v, hv, hvp⟩ := hpointSmall
  obtain ⟨z, hzJ, hzs⟩ := hinner hv
  have hzQt := N.support_target (interior_subset hzJ)
  have hzWr : N.chart.symm z ∈ N.window.right.target :=
    N.window.right_target.symm.subset ((N.chart_inside (N.chart.map_target hzQt)).2)
  have hpoint : p (d x) = N.chart.symm z := by
    change p v = p (d x) at hvp
    rw [← hvp, ← hzs]
    change p (N.window.right.symm (N.chart.symm z)) = N.chart.symm z
    exact (congrFun N.window.right_eq _).symm.trans (N.window.right.right_inv hzWr)
  have hxQ : p (d x) ∈ N.chart.source := hpoint.symm ▸ N.chart.map_target hzQt
  obtain ⟨hleftPoint, hrightPoint⟩ := twoBranchWindow_double_images N.window
    (mem_image_of_mem d (hAnn.subset x.property)) (mem_image_of_mem d (hAnn.subset y.property))
    hne hpair ((N.chart_inside hxQ).2)
  have hzvalue : N.chart (p (d x)) = z := by rw [hpoint, N.chart.right_inv hzQt]
  have hplanes : 0 ≤ (N.coordinates z).1.1 ∧ (N.coordinates z).2 = 0 := by
    rw [hleftimage] at hleftPoint
    have h := (N.left_halfplane _ hxQ).mp hleftPoint
    rwa [hzvalue] at h
  have hzB : z ∈ B.space := by
    rw [hBs]
    obtain ⟨v, ⟨hvD, hvR⟩, hvp⟩ := hrightPoint
    refine ⟨⟨v, ⟨hvD, hvR, ?_⟩, ?_⟩, interior_subset hzJ⟩
    · change N.window.right v ∈ N.chart.source
      rw [congrFun N.window.right_eq v, hvp]
      exact hxQ
    · change N.chart (N.window.right v) = z
      rw [congrFun N.window.right_eq v, hvp]
      exact hzvalue
  have hzW : N.chart.symm z ∈ W := (N.chart_inside (N.chart.map_target hzQt)).1
  by_cases hz0 : (N.coordinates z).1.1 = 0
  · have hzK : z ∈ K.space := hKzero.symm ▸ ⟨hzB, hz0⟩
    obtain ⟨T, hzT, _hT0, hTW, hTPL, _hpre, hreg, hfront, hleft, hright⟩ :=
      hcross z hzK hzJ hplanes.2 W hWopen hzW
    obtain ⟨Cross, hCs⟩ := ProjectedSourceCrossing.exists_of_linear_coordinates
      s.charts p d D.K.space (s.projection ⁻¹' R) x y N.window T
      (N.coordinates.trans crossingCoordinates) hne hpair (hpoint.symm ▸ hzT)
      (fun _ hz ↦ (N.chart_inside (hTW hz).2).2) hTPL
      (fun v hv ↦ (by
        rw [hAnn]
        exact (hleft v hv).trans (by
          change (0 ≤ (N.coordinates (T v)).2 ∧ (N.coordinates (T v)).1.1 = 0) ↔
            (N.coordinates (T v)).1.1 = 0 ∧ v ∈ s.projection ⁻¹' R
          rw [hreg v hv]
          exact and_comm)))
      (fun v hv ↦ (by
        rw [hAnn]
        exact (hright v hv).trans (by
          change (0 ≤ (N.coordinates (T v)).2 ∧ (N.coordinates (T v)).1.2 = 0) ↔
            (N.coordinates (T v)).1.2 = 0 ∧ v ∈ s.projection ⁻¹' R
          rw [hreg v hv]
          exact and_comm))) (Or.inr ⟨hreg, hfront⟩)
    exact ⟨Cross, fun v hv ↦ (hTW (hCs ▸ hv)).1⟩
  · have hzpos : 0 < (N.coordinates z).1.1 := lt_of_le_of_ne hplanes.1 (Ne.symm hz0)
    obtain ⟨T, hzT, _hT0, hTW, hTPL, _hpre, hleft, hright⟩ :=
      N.exists_positive_whole_crossing hAnn hW B' (hHK.embeddedImage_faces _)
        (hB's.symm.subset hzB) hzJ hzpos hplanes.2 W hWopen hzW
    have hTin : T.source ⊆ interior (s.projection ⁻¹' R) := fun _ hv ↦ (hTW hv).2.2
    obtain ⟨Cross, hCs⟩ := ProjectedSourceCrossing.exists_of_linear_coordinates
      s.charts p d D.K.space (s.projection ⁻¹' R) x y N.window T
      (N.coordinates.trans crossingCoordinatesRightLast) hne hpair (hpoint.symm ▸ hzT)
      (fun _ hz ↦ (N.chart_inside (hTW hz).2.1).2) hTPL
      (fun v hv ↦ (by
        rw [hAnn]
        exact (hleft v hv).trans
          ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩))
      (fun v hv ↦ (by
        rw [hAnn]
        exact (hright v hv).trans
          ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩))
      (Or.inl hTin)
    exact ⟨Cross, fun v hv ↦ (hTW (hCs ▸ hv)).1⟩

end Geometry.OriginalPLTower
