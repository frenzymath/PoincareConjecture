import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalInteriorCrossings
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

theorem OriginalGeneralPositionData.exists_interior_exception_repair
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (a b : D2) (hab : a ≠ b) (haint : (a : V2) ∉ Q2)
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
  obtain ⟨w, c, Q, J, K, K₀, H, G, new, ρ,
    _ha, _hb, _haQ, _hQzero, hQU, hQw, _hQPL, _hJ, _hK, hJQ, _hzeroJ,
    _hρ, _hclosed, _hKold, _hcollar, hSmall, hSmallInner,
    _hSmallEnd, hSmallEndInner, hcenter, hSmallFix,
    hG, hGinv, hGzero, _hformula, hGout, _hGprotected, _hGleft, hGfront, hGregion,
    hGPL, hnewmap, _hrim, _hnewpath, _hrimpoint, hnewimage, hleft, hcross, _relation⟩ :=
    data.exists_interior_crossed_charts_with_closed_support he hF hopen
      a b hab haint hpair U hU haU 1 zero_lt_one
  let p := step.projection ∘ step.inclusion
  have hwr : (w.right : t.Carrier → s.Carrier) = p := w.right_eq
  let Small := (w.right.trans Q).symm '' closedBall (0 : V3) ρ
  have hSmallU : Small ⊆ p ⁻¹' U :=
    hSmallInner.trans (right_branch_chart_support_subset w Q
      (interior_subset.trans hJQ) hQw (fun _ hz ↦ (hQU hz).1))
  have hmark (u : I) : (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark := by
    have hfix : EqOn (G u) id (t.projection ⁻¹' Fmark) := by
      apply (hGfront u).mono
      rw [t.frontier_region R]
      exact preimage_mono hF
    ext x
    constructor
    · intro hx
      change G u x ∈ t.projection ⁻¹' Fmark at hx
      have hval : G u x = x := (G u).injective (hfix hx)
      simpa only [hval] using hx
    · intro hx
      change G u x ∈ t.projection ⁻¹' Fmark
      simpa only [hfix hx, id_eq] using hx
  have hnew : new.map = G 1 ∘ data.initial.map := funext hnewmap
  refine ⟨G, Small, hG, hGinv, hGzero, hGPL 1, hGregion, hmark,
    fun u ↦ right_branch_motion_fixed_off_window w Q hJQ hQw
      (fun _ hz ↦ (hQU hz).1) (hGout u), hSmall, hSmallU, hSmallFix, hcenter, ?_⟩
  intro x y hxy hpointpair hpointSmall
  rw [← hnewmap x, ← hnewmap y] at hpointpair
  rw [← hnewmap x] at hpointSmall
  rw [← hnew]
  change p (new.map x) = p (new.map y) at hpointpair
  obtain ⟨v, hv, hvp⟩ := hpointSmall
  change p v = p (new.map x) at hvp
  obtain ⟨z, hzJ, hzs⟩ := hSmallEndInner hv
  have hzQt := hJQ (interior_subset hzJ)
  have hzW : Q.symm z ∈ w.right.target :=
    w.right_target.symm ▸ hQw (Q.map_target hzQt)
  have hpoint : p (new.map x) = Q.symm z := by
    rw [← hvp, ← hzs]
    change p (w.right.symm (Q.symm z)) = Q.symm z
    rw [← hwr, w.right.right_inv hzW]
  have hxQ : p (new.map x) ∈ Q.source := hpoint.symm ▸ Q.map_target hzQt
  have hne : new.map x ≠ new.map y := fun h ↦ hxy (new.embedding.injective h)
  obtain ⟨hleftPoint, hrightPoint⟩ := twoBranchWindow_double_images w
    (mem_image_of_mem new.map x.property) (mem_image_of_mem new.map y.property)
    hne hpointpair (hQw hxQ)
  have hzvalue : Q (p (new.map x)) = z := by rw [hpoint, Q.right_inv hzQt]
  have hz0 : (c z).2 = 0 := by
    have h := (hleft _ hxQ).mp hleftPoint
    rwa [hzvalue] at h
  have hzK : z ∈ H.map 1 '' K.space := by
    apply hnewimage.subset
    obtain ⟨v, ⟨hvD, hvR⟩, hvp⟩ := hrightPoint
    change p v = p (new.map x) at hvp
    refine ⟨⟨v, ⟨hvD, hvR, ?_⟩, ?_⟩, interior_subset hzJ⟩
    · change w.right v ∈ Q.source
      rw [hwr, hvp]
      exact hxQ
    · change Q (w.right v) = z
      rw [hwr, hvp]
      exact hzvalue
  have hzU : Q.symm z ∈ U := (hQU (Q.map_target hzQt)).1
  obtain ⟨T, hzT, _hT0, hTU, hTPL, _hpre, hleftT, hrightT⟩ :=
    hcross z hzK hzJ hz0 U hU hzU
  have hTin : T.source ⊆ interior (s.projection ⁻¹' R) := fun _ hv ↦ (hTU hv).2.2
  obtain ⟨B, hBs⟩ := exists_projected_crossing_of_linear_coordinates s.charts p new.map
    (s.projection ⁻¹' R) x y w T (c.trans crossingCoordinatesLeftLast) hne hpointpair
    (hpoint.symm ▸ hzT) (fun _ hz ↦ hQw (hTU hz).2.1) hTPL
    (fun v hv ↦ (hleftT v hv).trans
      ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩)
    (fun v hv ↦ (hrightT v hv).trans
      ⟨fun h ↦ ⟨h, interior_subset (hTin hv)⟩, And.left⟩)
    (Or.inl hTin)
  exact ⟨B, fun v hv ↦ (hTU (hBs ▸ hv)).1⟩

end Geometry.OriginalPLTower
