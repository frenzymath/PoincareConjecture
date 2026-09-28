import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusOpenChart
import PoincareConjecture.Proofs.M76.Mathlib.TorusPLCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

theorem depth_centered (x : ℝ × ℝ) :
    PLAnnularStrip.depth (7 / 2) (x + ((7 / 4 : ℝ), (7 / 4 : ℝ))) =
      7 / 4 - ‖x‖ := by
  change min (min (x.1 + 7 / 4) (x.2 + 7 / 4))
    (min (7 / 2 - (x.1 + 7 / 4)) (7 / 2 - (x.2 + 7 / 4))) = _
  rw [show (7 / 2 : ℝ) - (x.1 + 7 / 4) = 7 / 4 - x.1 by ring,
    show (7 / 2 : ℝ) - (x.2 + 7 / 4) = 7 / 4 - x.2 by ring,
    show x.1 + (7 / 4 : ℝ) = 7 / 4 - -x.1 by ring,
    show x.2 + (7 / 4 : ℝ) = 7 / 4 - -x.2 by ring]
  rw [show min (min ((7 / 4 : ℝ) - -x.1) (7 / 4 - -x.2))
      (min (7 / 4 - x.1) (7 / 4 - x.2)) =
      min (min (7 / 4 - x.1) (7 / 4 - -x.1))
        (min (7 / 4 - x.2) (7 / 4 - -x.2)) by ac_rfl]
  simp only [min_sub_sub_left, ← abs_eq_max_neg, Prod.norm_def, Real.norm_eq_abs]




theorem exists_square_shell_radial_chart {v : ℝ × ℝ}
    (hv : ‖v‖ ∈ Icc (3 / 2 : ℝ) 2) :
    ∃ P : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      v ∈ P.target ∧ P ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
        ∀ w ∈ P.source, ‖P w‖ = 7 / 4 - w.2 := by
  let : Fact (0 < 4 * (7 / 2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨e, heS, heval, hePL⟩ := PLAnnularStrip.exists_annulus_PL_openPartialHomeomorph
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : 4 * (1 / 2 : ℝ) < 7 / 2)
  have hvdepth : PLAnnularStrip.depth (7 / 2)
      (v + ((7 / 4 : ℝ), (7 / 4 : ℝ))) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [depth_centered]
    constructor <;> linarith [hv.1, hv.2]
  change v + ((7 / 4 : ℝ), (7 / 4 : ℝ)) ∈
    PLAnnularStrip.depth (7 / 2) ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2) at hvdepth
  rw [← PLAnnularStrip.range_annulusMap_open
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : 4 * (1 / 2 : ℝ) < 7 / 2)] at hvdepth
  obtain ⟨⟨z, t⟩, hzt⟩ := hvdepth
  change PLAnnularStrip.annulusMap (7 / 2) (by norm_num) (z, (t : ℝ)) =
    v + ((7 / 4 : ℝ), (7 / 4 : ℝ)) at hzt
  obtain ⟨b, hb⟩ := AddCircle.two_puncture_charts_cover (4 * (7 / 2 : ℝ)) z
  let a : ℝ := if b then 0 else (4 * (7 / 2)) / 2
  let Q := (AddCircle.openPartialHomeomorphCoe (4 * (7 / 2 : ℝ)) a).prod
    (OpenPartialHomeomorph.refl ℝ)
  let τ : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (-((7 / 4 : ℝ), (7 / 4 : ℝ)))
  let P := (Q.trans e).transHomeomorph τ.toHomeomorph
  have hQzt : (z, (t : ℝ)) ∈ Q.target := ⟨hb, mem_univ _⟩
  have hezt : (z, (t : ℝ)) ∈ e.source := by
    rw [heS]
    exact ⟨mem_univ _, t.property⟩
  have hsource : Q.symm (z, (t : ℝ)) ∈ (Q.trans e).source := by
    refine ⟨Q.map_target hQzt, ?_⟩
    change Q (Q.symm (z, (t : ℝ))) ∈ e.source
    rw [Q.right_inv hQzt]
    exact hezt
  have hPvalue : P (Q.symm (z, (t : ℝ))) = v := by
    change τ (e (Q (Q.symm (z, (t : ℝ))))) = v
    rw [Q.right_inv hQzt, heval, hzt]
    change -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
      (v + ((7 / 4 : ℝ), (7 / 4 : ℝ))) = v
    abel
  have hvP : v ∈ P.target := by
    rw [← hPvalue]
    exact P.map_source hsource
  have hPPL : P ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
    apply (mem_piecewiseAffineGroupoid_iff_forward P).mpr
    have h := (locallyPiecewiseAffineOn_affine τ.toContinuousAffineMap isOpen_univ).comp
      (hePL a).1
    change LocallyPiecewiseAffineOn (fun x => τ (e (Q x))) (Q.trans e).source
    simpa only [preimage_univ, inter_univ, Function.comp_def,
      ContinuousAffineEquiv.coe_toContinuousAffineMap,
      OpenPartialHomeomorph.trans_apply] using h
  refine ⟨P, hvP, hPPL, ?_⟩
  intro w hw
  have hwe : Q w ∈ e.source := hw.2
  have hwt : w.2 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [heS] at hwe
    exact hwe.2
  have habs : 4 * |w.2| < (7 / 2 : ℝ) := by
    have h := abs_lt.mpr hwt
    linarith
  have hdepth := PLAnnularStrip.depth_annulusMap
    (by norm_num : (0 : ℝ) < 7 / 2) habs (Q w).1
  have hcenter : P w + ((7 / 4 : ℝ), (7 / 4 : ℝ)) =
      PLAnnularStrip.annulusMap (7 / 2) (by norm_num) ((Q w).1, w.2) := by
    change τ (e (Q w)) + ((7 / 4 : ℝ), (7 / 4 : ℝ)) = _
    rw [heval]
    change -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
      PLAnnularStrip.annulusMap (7 / 2) (by norm_num) (Q w) +
      ((7 / 4 : ℝ), (7 / 4 : ℝ)) = _
    change -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
      PLAnnularStrip.annulusMap (7 / 2) (by norm_num) ((Q w).1, w.2) +
      ((7 / 4 : ℝ), (7 / 4 : ℝ)) = _
    abel
  have h := depth_centered (P w)
  rw [hcenter, hdepth] at h
  linarith

end PoincareConjecture.M76.HamiltonIndexOne
