import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.M25.Topology3D

variable (v : ℝ → ℝ) {K L : ℝ≥0}
variable (hK : LipschitzWith K v) (hL : ∀ z, ‖v z‖ ≤ L)




theorem boundedFlow_strictMono (hv : ContDiff ℝ ∞ v) (hs : HasCompactSupport v)
    (t : ℝ) : StrictMono (fun z => boundedFlow v hK hL z t) := by
  obtain ⟨R, hR, hsub⟩ := hs.isBounded.subset_ball_lt 0 (0 : ℝ)
  have hzero (z : ℝ) (hz : R ≤ |z|) : v z = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hzs
    have hlt : |z| < R := by
      simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using hsub hzs
    exact (not_lt_of_ge hz) hlt
  have hp : boundedFlow v hK hL R t = R :=
    boundedFlow_eq_self v hK hL R (hzero R (by rw [abs_of_pos hR])) t
  have hm : boundedFlow v hK hL (-R) t = -R :=
    boundedFlow_eq_self v hK hL (-R) (hzero (-R) (by rw [abs_neg, abs_of_pos hR])) t
  have hc : Continuous (fun z => boundedFlow v hK hL z t) :=
    ((boundedFlow_contDiff v hK hL hv hs).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  rcases hc.strictMono_of_inj (boundedFlow_injective v hK hL t) with hmono | hanti
  · exact hmono
  · have hbad := hanti (show -R < R by linarith)
    change boundedFlow v hK hL R t < boundedFlow v hK hL (-R) t at hbad
    rw [hp, hm] at hbad
    linarith





theorem boundedFlow_eq_scalar_contraction (c r R z : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hlower : r ≤ Real.exp (-t) * |z - c|)
    (hupper : |z - c| ≤ R)
    (hag : EqOn v (fun w => c - w) {w | r ≤ |w - c| ∧ |w - c| ≤ R}) :
    boundedFlow v hK hL z t = c + Real.exp (-t) * (z - c) := by
  have htrack (s : ℝ) (hs : s ∈ Icc 0 t) :
      c + Real.exp (-s) * (z - c) ∈ {w | r ≤ |w - c| ∧ |w - c| ≤ R} := by
    have habs : |c + Real.exp (-s) * (z - c) - c| = Real.exp (-s) * |z - c| := by
      rw [add_sub_cancel_left, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mem_ofPred_eq, habs]
    constructor
    · exact hlower.trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by linarith [hs.2])) (abs_nonneg _))
    · exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (by linarith [hs.1])) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hupper)
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) : HasDerivAt
      (fun w => c + Real.exp (-w) * (z - c))
      (v (c + Real.exp (-s) * (z - c))) s := by
    rw [hag (htrack s hs)]
    convert! (((hasDerivAt_id s).neg.exp).mul_const (z - c)).const_add c using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  have heq : EqOn (boundedFlow v hK hL z)
      (fun s => c + Real.exp (-s) * (z - c)) (Icc 0 t) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ w => v w) (s := fun _ => univ) (fun _ _ => hK.lipschitzOnWith)
    · exact fun s _ =>
        (boundedFlow_hasDerivAt v hK hL z s).continuousAt.continuousWithinAt
    · exact fun s _ => (boundedFlow_hasDerivAt v hK hL z s).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · rw [boundedFlow_zero, neg_zero, Real.exp_zero]
      ring
  exact heq ⟨ht, le_rfl⟩

end PoincareConjecture.M25.Topology3D
