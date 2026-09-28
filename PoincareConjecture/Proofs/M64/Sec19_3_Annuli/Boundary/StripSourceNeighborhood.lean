import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusSourceCoordinates
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.PeriodicStripEquation

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M64

theorem annulusBoundarySource_mapsTo_closedStrip (r x : ℝ) (hr : r ≠ 0)
    {R : ℝ} (hR : R < 1) (upper : Bool) :
    MapsTo (annulusBoundarySource r hr upper x)
      (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})
      {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} := by
  intro z hz
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz.1
  have him := (le_abs_self z.im).trans (z.abs_im_le_norm.trans hn)
  have hy : 0 ≤ z.im := hz.2
  rw [annulusBoundarySource_apply]
  change (if upper then 1 - z.im else z.im) ∈ Icc (0 : ℝ) 1
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true, mem_Icc]
  · exact ⟨hy, him.trans hR.le⟩
  · exact ⟨by linarith, by linarith⟩

theorem annulusBoundarySource_mapsTo_openStrip (r x : ℝ) (hr : r ≠ 0)
    {R : ℝ} (hR : R < 1) (upper : Bool) :
    MapsTo (annulusBoundarySource r hr upper x)
      (ball (0 : ℂ) R ∩ {z | 0 < z.im}) m64AnnulusOpenStrip := by
  intro z hz
  have hn : ‖z‖ < R := mem_ball_zero_iff.mp hz.1
  have him := (le_abs_self z.im).trans (z.abs_im_le_norm.trans hn.le)
  have hy : 0 < z.im := hz.2
  rw [annulusBoundarySource_apply]
  change 0 < (if upper then 1 - z.im else z.im) ∧
    (if upper then 1 - z.im else z.im) < 1
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact ⟨hy, him.trans_lt hR⟩
  · exact ⟨by linarith, by linarith⟩

theorem annulusBoundarySource_strip_radius (r x : ℝ) (hr : r ≠ 0) (upper : Bool)
    {O : Set LoopPlane} (hO : IsOpen O)
    (ha : annulusPoint x (if upper then 1 else 0) ∈ O) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ MapsTo (annulusBoundarySource r hr upper x)
      (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) O := by
  have hc : Continuous (annulusBoundarySource r hr upper x) :=
    continuous_const.add (annulusBoundaryLinear r hr upper).continuous
  have hcenter : annulusBoundarySource r hr upper x 0 ∈ O := by
    simpa only [annulusBoundarySource, map_zero, add_zero] using ha
  obtain ⟨e, he, hesub⟩ := nhds_basis_closedBall.mem_iff.mp
    (hc.continuousAt.eventually (hO.mem_nhds hcenter))
  let R := min e 1 / 2
  have hR : 0 < R := half_pos (lt_min he zero_lt_one)
  have hsmall : R < min e 1 := half_lt_self (lt_min he zero_lt_one)
  exact ⟨R, hR, hsmall.trans_le (min_le_right _ _), fun z hz =>
    hesub (closedBall_subset_closedBall (hsmall.trans_le (min_le_left _ _)).le hz.1)⟩

end PoincareConjecture.M64
