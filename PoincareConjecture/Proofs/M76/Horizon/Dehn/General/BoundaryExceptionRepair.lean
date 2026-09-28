import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalBoundaryCrossings
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ProjectedCrossingCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchMotionSupport










set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
  {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
  {old : StageMarkedDisk t R Fmark base Jgroup}



theorem OriginalGeneralPositionData.exists_boundary_exception_repair
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (a b : D2) (hab : a ≠ b) (haRim : (a : V2) ∈ Q2)
    (hpair : step.projection (step.inclusion (data.initial.map a)) =
      step.projection (step.inclusion (data.initial.map b)))
    (U : Set s.Carrier) (hU : IsOpen U)
    (haU : step.projection (step.inclusion (data.initial.map a)) ∈ U) :
    ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (Small : Set t.Carrier),
      Continuous (fun z : I × t.Carrier ↦ G z.1 z.2) ∧
      Continuous (fun z : I × t.Carrier ↦ (G z.1).symm z.2) ∧
      (∀ x, G 0 x = x) ∧
      (∀ i j, (t.charts i).symm.trans
        ((G 1).toOpenPartialHomeomorph.trans (t.charts j)) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
      (∀ u, (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
      (∀ u, EqOn (G u) id ((step.projection ∘ step.inclusion) ⁻¹' U)ᶜ) ∧
      IsCompact Small ∧ Small ⊆ (step.projection ∘ step.inclusion) ⁻¹' U ∧
      (∀ u, EqOn (G u) id (data.initial.map '' D2 \ Small)) ∧
      step.projection (step.inclusion (data.initial.map a)) ∈
        (step.projection ∘ step.inclusion) '' Small ∧
      ∀ x y : D2, x ≠ y →
        step.projection (step.inclusion (G 1 (data.initial.map x))) =
          step.projection (step.inclusion (G 1 (data.initial.map y))) →
        step.projection (step.inclusion (G 1 (data.initial.map x))) ∈
          (step.projection ∘ step.inclusion) '' (Small ∪ G 1 '' Small) →
        ∃ B : ProjectedDiskCrossing s.charts (step.projection ∘ step.inclusion)
          (G 1 ∘ data.initial.map) (s.projection ⁻¹' R) x y,
          B.chart.source ⊆ U := by
  obtain ⟨w, c, Q, J, C₀, B, K, q, H, G, new, eta,
    _ha, _hb, _haQ, _hQzero, hQU, _hJ, hJQ, _hQPL, _hbranches, _hwhole,
    hG, hGinv, hGzero, _hformula, hGout, _hGprotected, _hGleft, hGregion,
    hGPL, hnewmap, _hpath, _hB, _hK, _hKB, hBs, _hKs, hKzero,
    _hqB, _hqi, _hqD, _hqrim, _hvertices, hcross, hinterior,
    ⟨Small, hSmall, _hSmallEnd, hSmallInner, hcenter, hSmallFix⟩,
    _history, _hregion, _holdplane, hnewplane, _hbad, _relation⟩ :=
    data.exists_boundary_operation_crossed_charts step he hF hopen old
      a b hab haRim hpair U hU haU 1 zero_lt_one
  let p := step.projection ∘ step.inclusion
  have hwr : (w.right : t.Carrier → s.Carrier) = p := w.right_eq
  have hQw : Q.source ⊆ w.target := fun _ hz ↦ (hQU hz).2
  have hSmallU : Small ⊆ p ⁻¹' U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hSmallInner (Or.inl hx)
    have hzQ := hJQ (interior_subset hz)
    have hzW : Q.symm z ∈ w.right.target :=
      w.right_target.symm ▸ hQw (Q.map_target hzQ)
    change p (w.right.symm (Q.symm z)) ∈ U
    rw [← congrFun hwr _, w.right.right_inv hzW]
    exact (hQU (Q.map_target hzQ)).1
  have hnew : new.map = G 1 ∘ data.initial.map := funext hnewmap
  refine ⟨G, Small, hG, hGinv, hGzero, hGPL 1,
    fun u ↦ (hGregion u).1, fun u ↦ (hGregion u).2.2,
    fun u ↦ right_branch_motion_fixed_off_window w Q hJQ hQw
      (fun _ hz ↦ (hQU hz).1) (hGout u), hSmall, hSmallU, hSmallFix, hcenter, ?_⟩
  intro x y hxy hpointpair hpointSmall
  rw [← hnew]
  simp only [← hnewmap] at hpointpair hpointSmall
  change p (new.map x) = p (new.map y) at hpointpair
  obtain ⟨v, hv, hvp⟩ := hpointSmall
  change p v = p (new.map x) at hvp
  obtain ⟨z, hzJ, hzs⟩ := hSmallInner hv
  have hzQt := hJQ (interior_subset hzJ)
  have hzW : Q.symm z ∈ w.right.target :=
    w.right_target.symm ▸ hQw (Q.map_target hzQt)
  have hpoint : p (new.map x) = Q.symm z := by
    rw [← hvp, ← hzs]
    change p (w.right.symm (Q.symm z)) = Q.symm z
    rw [← congrFun hwr _, w.right.right_inv hzW]
  have hxQ : p (new.map x) ∈ Q.source := hpoint.symm ▸ Q.map_target hzQt
  have hne : new.map x ≠ new.map y := fun h ↦ hxy (new.embedding.injective h)
  obtain ⟨hleft, hright⟩ := twoBranchWindow_double_images w
    (mem_image_of_mem new.map x.property) (mem_image_of_mem new.map y.property)
    hne hpointpair (hQw hxQ)
  have hplanes := (hnewplane _ hxQ).mp hleft
  have hzvalue : Q (p (new.map x)) = z := by rw [hpoint, Q.right_inv hzQt]
  rw [hzvalue] at hplanes
  have hzB : z ∈ B.space := by
    rw [hBs]
    obtain ⟨v, ⟨hvD, hvR⟩, hvp⟩ := hright
    change p v = p (new.map x) at hvp
    refine ⟨⟨v, ⟨hvD, hvR, ?_⟩, ?_⟩, interior_subset hzJ⟩
    · change w.right v ∈ Q.source
      rw [hwr, hvp]
      exact hxQ
    · change Q (w.right v) = z
      rw [hwr, hvp]
      exact hzvalue
  have hzU : Q.symm z ∈ U := (hQU (Q.map_target hzQt)).1
  by_cases hz0 : (c z).1.1 = 0
  · have hzK : z ∈ K.space := hKzero.symm ▸ ⟨hzB, hz0⟩
    obtain ⟨T, hzT, _hT0, hTU, hTPL, _hpre, hreg, hfront, hleftT, hrightT⟩ :=
      hcross z hzK hzJ hplanes.2 U hU hzU
    obtain ⟨D, hDs⟩ := exists_projected_crossing_of_linear_coordinates s.charts p new.map
      (s.projection ⁻¹' R) x y w T (c.trans crossingCoordinates) hne hpointpair
      (hpoint.symm ▸ hzT) (fun _ hz ↦ hQw (hTU hz).2) hTPL
      (fun v hv ↦ (hleftT v hv).trans (by
        change (0 ≤ (c (T v)).2 ∧ (c (T v)).1.1 = 0) ↔
          (c (T v)).1.1 = 0 ∧ v ∈ s.projection ⁻¹' R
        rw [hreg v hv]
        exact and_comm))
      (fun v hv ↦ (hrightT v hv).trans (by
        change (0 ≤ (c (T v)).2 ∧ (c (T v)).1.2 = 0) ↔
          (c (T v)).1.2 = 0 ∧ v ∈ s.projection ⁻¹' R
        rw [hreg v hv]
        exact and_comm)) (Or.inr ⟨hreg, hfront⟩)
    exact ⟨D, fun v hv ↦ (hTU (hDs ▸ hv)).1⟩
  · have hzpos : 0 < (c z).1.1 := lt_of_le_of_ne hplanes.1 (Ne.symm hz0)
    obtain ⟨T, hzT, _hT0, hTU, hTPL, _hpre, hleftT, hrightT⟩ :=
      hinterior z hzB hzJ hzpos hplanes.2 U hU hzU
    have hTin : T.source ⊆ interior (s.projection ⁻¹' R) := fun _ hv ↦ (hTU hv).2.2
    obtain ⟨D, hDs⟩ := exists_projected_crossing_of_linear_coordinates s.charts p new.map
      (s.projection ⁻¹' R) x y w T (c.trans crossingCoordinatesRightLast) hne hpointpair
      (hpoint.symm ▸ hzT) (fun _ hz ↦ hQw (hTU hz).2.1) hTPL
      (fun v hv ↦ (hleftT v hv).trans
        ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩)
      (fun v hv ↦ (hrightT v hv).trans
        ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩)
      (Or.inl hTin)
    exact ⟨D, fun v hv ↦ (hTU (hDs ▸ hv)).1⟩

end Geometry.OriginalPLTower
