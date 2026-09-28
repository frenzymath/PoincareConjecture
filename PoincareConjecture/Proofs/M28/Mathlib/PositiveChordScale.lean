import PoincareConjecture.Proofs.M28.Sec10_5_Angles.ChordDefectLimits
import Mathlib.Topology.Order.LeftRightNhds










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M28




theorem exists_positive_rectangle_of_joint_limit
    {f : ℝ → ℝ → ℝ} {K kappa : ℝ}
    (hlimit : Tendsto (fun p : ℝ × ℝ => f p.1 p.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 K))
    (hkappa : kappa < K) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 < b ∧
      ∀ s ∈ Ioo (0 : ℝ) a, ∀ t ∈ Ioo (0 : ℝ) b, kappa < f s t := by
  have hgood : {p : ℝ × ℝ | kappa < f p.1 p.2} ∈
      (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)) :=
    hlimit.eventually (Ioi_mem_nhds hkappa)
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hgood
  obtain ⟨a, ha, hasub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hA
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hB
  exact ⟨a, ha, b, hb, fun s hs t ht =>
    hAB (show (s, t) ∈ A ×ˢ B from ⟨hasub hs, hbsub ht⟩)⟩




theorem half_mul_radius_sq_le_of_chord_lower
    {s t d kappa : ℝ} (hkappa : 0 ≤ kappa) (hkappa1 : kappa ≤ 1)
    (hchord : (s - t) ^ 2 + kappa * s * t ≤ d ^ 2) :
    (kappa / 2) * s ^ 2 ≤ d ^ 2 := by
  have hfactor : 0 ≤ 1 - kappa / 2 := by linarith only [hkappa1]
  have hfirst := mul_nonneg hfactor (sq_nonneg (s - t))
  have hsecond := mul_nonneg (div_nonneg hkappa (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg t)
  nlinarith only [hchord, hfirst, hsecond]




theorem scalar_radius_ratio_le_of_chord_lower
    {s t d kappa C sigma Q : ℝ}
    (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hsigma : 0 ≤ sigma) (hQ : 0 ≤ Q)
    (hchord : (s - t) ^ 2 + kappa * s * t ≤ d ^ 2)
    (hdistance : d ≤ C * sigma) (hnormal : Q * sigma ^ 2 ≤ 2) :
    Q * s ^ 2 ≤ 4 * C ^ 2 / kappa := by
  have hcoercive := half_mul_radius_sq_le_of_chord_lower hkappa.le hkappa1 hchord
  have hsquare : d ^ 2 ≤ (C * sigma) ^ 2 := by
    have hmul := mul_le_mul hdistance hdistance hd (mul_nonneg hC hsigma)
    simpa only [← pow_two] using hmul
  have hscaled := mul_le_mul_of_nonneg_left (hcoercive.trans hsquare) hQ
  have hcap := mul_le_mul_of_nonneg_left hnormal (sq_nonneg C)
  apply (le_div_iff₀ hkappa).mpr
  nlinarith only [hscaled, hcap]

end PoincareConjecture.M28
