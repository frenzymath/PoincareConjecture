import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusOpenChart
import PoincareConjecture.Proofs.M76.Mathlib.TorusPLCharts

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_planar_annulus_depth_chart {x : V} (hx : x ∈ Ann) :
    ∃ H : OpenPartialHomeomorph V V,
      x ∈ H.source ∧ H x = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      ∀ y ∈ H.source, (H y).2 = depth 8 y - depth 8 x := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨e, hes, hev, hePL⟩ := exists_annulus_PL_openPartialHomeomorph
    (L := (8 : ℝ)) (d := (3 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hxrange := (range_annulusMap (L := (8 : ℝ)) (d := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)).symm.subset hx
  obtain ⟨⟨z, t⟩, hxt⟩ := hxrange
  obtain ⟨b, hb⟩ := AddCircle.two_puncture_charts_cover (4 * (8 : ℝ)) z
  let a : ℝ := if b then 0 else (4 * (8 : ℝ)) / 2
  let Q := (AddCircle.openPartialHomeomorphCoe (4 * (8 : ℝ)) a).prod
    (OpenPartialHomeomorph.refl ℝ)
  let E := Q.trans e
  let p : V := ((AddCircle.openPartialHomeomorphCoe (4 * (8 : ℝ)) a).symm z, t)
  have hpQ : p ∈ Q.source :=
    ⟨(AddCircle.openPartialHomeomorphCoe (4 * (8 : ℝ)) a).map_target hb, mem_univ _⟩
  have hQp : Q p = (z, (t : ℝ)) := by
    apply Prod.ext
    · exact (AddCircle.openPartialHomeomorphCoe (4 * (8 : ℝ)) a).right_inv hb
    · rfl
  have hpE : p ∈ E.source := by
    refine ⟨hpQ, ?_⟩
    change Q p ∈ e.source
    rw [hQp, hes]
    exact ⟨mem_univ _, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hEp : E p = x := by
    change e (Q p) = x
    rw [hQp, hev]
    exact hxt
  have hxE : x ∈ E.target := hEp ▸ E.map_source hpE
  have hEPL : E ∈ piecewiseAffineGroupoid V := hePL a
  have hdepth (y : V) (hy : y ∈ E.target) : (E.symm y).2 = depth 8 y := by
    have hp := E.map_target hy
    have ht : (E.symm y).2 ∈ Ioo (-(3 / 2 : ℝ)) (3 / 2 : ℝ) := by
      have hh := hp.2
      rw [hes] at hh
      exact hh.2
    have hwidth : 4 * |(E.symm y).2| < (8 : ℝ) := by
      have hh := abs_lt.mpr ht
      linarith
    have hvalue : E (E.symm y) =
        annulusMap 8 (by norm_num)
          (((E.symm y).1 : AddCircle (4 * (8 : ℝ))), (E.symm y).2) := by
      change e (Q (E.symm y)) = _
      rw [hev]
      rfl
    calc
      (E.symm y).2 = depth 8 (E (E.symm y)) := by
        rw [hvalue, depth_annulusMap (by norm_num) hwidth]
      _ = depth 8 y := congrArg (depth 8) (E.right_inv hy)
  let A := ContinuousAffineEquiv.constVAdd ℝ V (-(E.symm x))
  let H := E.symm.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hHs : H.source = E.target := by
    change E.target ∩ E.symm ⁻¹' (univ : Set V) = E.target
    rw [preimage_univ, inter_univ]
  refine ⟨H, hHs.symm.subset hxE, ?_,
    (locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ).comp hEPL.2,
    hEPL.1.comp (locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ), ?_⟩
  · change -E.symm x + E.symm x = 0
    exact neg_add_cancel _
  · intro y hy
    change -(E.symm x).2 + (E.symm y).2 = _
    rw [hdepth x hxE, hdepth y (hHs.subset hy)]
    ring

theorem exists_planar_annulus_boundary_chart {x : V} (hx : x ∈ Ann)
    (hrim : depth 8 x = -1 ∨ depth 8 x = 1) :
    ∃ (H : OpenPartialHomeomorph V V) (B : V →ₗ[ℝ] ℝ),
      x ∈ H.source ∧ H x = 0 ∧ B ≠ 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ y ∈ H.source, y ∈ Ann ↔ 0 ≤ B (H y)) ∧
      ∀ y ∈ H.source, (depth 8 y = -1 ∨ depth 8 y = 1) ↔ B (H y) = 0 := by
  obtain ⟨G, hxG, hGx, hG, hGi, hdepth⟩ := exists_planar_annulus_depth_chart hx
  rcases hrim with hxneg | hxpos
  · let U : Set V := {y | depth 8 y < 0}
    have hU : IsOpen U := isOpen_lt (continuous_depth 8) continuous_const
    let H := G.restrOpen U hU
    let B : V →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ
    have hxU : x ∈ U := by change depth 8 x < 0; rw [hxneg]; norm_num
    refine ⟨H, B, ⟨hxG, hxU⟩, hGx, ?_,
      hG.mono H.open_source (fun _ hy => hy.1),
      hGi.mono H.open_target (fun _ hy => hy.1), ?_, ?_⟩
    · intro hB
      have h := LinearMap.congr_fun hB ((0 : ℝ), 1)
      norm_num [B] at h
    · intro y hy
      rw [mem_squareAnnulus_iff_depth]
      have hv : B (H y) = depth 8 y + 1 := by
        change (G y).2 = _
        rw [hdepth y hy.1, hxneg]
        ring
      rw [hv]
      have hyU : depth 8 y < 0 := hy.2
      constructor
      · intro hh; linarith [hh.1]
      · intro hh; constructor <;> linarith
    · intro y hy
      have hv : B (H y) = depth 8 y + 1 := by
        change (G y).2 = _
        rw [hdepth y hy.1, hxneg]
        ring
      rw [hv]
      have hyU : depth 8 y < 0 := hy.2
      constructor
      · rintro (hh | hh) <;> linarith
      · intro hh; left; linarith
  · let U : Set V := {y | 0 < depth 8 y}
    have hU : IsOpen U := isOpen_lt continuous_const (continuous_depth 8)
    let H := G.restrOpen U hU
    let B : V →ₗ[ℝ] ℝ := -(LinearMap.snd ℝ ℝ ℝ)
    have hxU : x ∈ U := by change 0 < depth 8 x; rw [hxpos]; norm_num
    refine ⟨H, B, ⟨hxG, hxU⟩, hGx, ?_,
      hG.mono H.open_source (fun _ hy => hy.1),
      hGi.mono H.open_target (fun _ hy => hy.1), ?_, ?_⟩
    · intro hB
      have h := LinearMap.congr_fun hB ((0 : ℝ), 1)
      norm_num [B] at h
    · intro y hy
      rw [mem_squareAnnulus_iff_depth]
      have hv : B (H y) = 1 - depth 8 y := by
        change -(G y).2 = _
        rw [hdepth y hy.1, hxpos]
        ring
      rw [hv]
      have hyU : 0 < depth 8 y := hy.2
      constructor
      · intro hh; linarith [hh.2]
      · intro hh; constructor <;> linarith
    · intro y hy
      have hv : B (H y) = 1 - depth 8 y := by
        change -(G y).2 = _
        rw [hdepth y hy.1, hxpos]
        ring
      rw [hv]
      have hyU : 0 < depth 8 y := hy.2
      constructor
      · rintro (hh | hh) <;> linarith
      · intro hh; right; linarith

end PoincareConjecture.M76.Dehn
