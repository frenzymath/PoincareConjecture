import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ScalarHeightFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_scalar_height_compression (c d R k : ℝ)
    (hd : 0 < d) (hdR : d ≤ R) (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      ∃ (K L : ℝ≥0) (hK : LipschitzWith K v) (hL : ∀ z, ‖v z‖ ≤ L)
        (T δ : ℝ), 0 ≤ T ∧ 0 < δ ∧
        (∀ t z, |z - c| ≤ δ → boundedFlow v hK hL z t = z) ∧
        (∀ z, d ≤ |z - c| → |z - c| ≤ R →
          boundedFlow v hK hL z T = c + k * (z - c)) ∧
        ∀ z, |z - c| ≤ R → |boundedFlow v hK hL z T - c| ≤ k * R := by
  let δ := k * d / 4
  let r := k * d / 2
  let T := -Real.log k
  have hR : 0 < R := hd.trans_le hdR
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by dsimp [δ, r]; nlinarith [mul_pos hk hd]
  have hrkd : r ≤ k * d := by dsimp [r]; nlinarith [mul_pos hk hd]
  have hT : 0 ≤ T := neg_nonneg.mpr (Real.log_nonpos hk.le hk1)
  have hexp : Real.exp (-T) = k := by
    dsimp [T]
    rw [neg_neg, Real.exp_log hk]
  let C : Set ℝ := {z | r ≤ |z - c| ∧ |z - c| ≤ 2 * R}
  let U : Set ℝ := {z | δ < |z - c| ∧ |z - c| < 3 * R}
  have habs : Continuous (fun z : ℝ => |z - c|) :=
    (continuous_id.sub continuous_const).abs
  have hCclosed : IsClosed C :=
    (isClosed_le continuous_const habs).inter (isClosed_le habs continuous_const)
  have hC : IsCompact C := (isCompact_closedBall c (2 * R)).of_isClosed_subset
    hCclosed (by
      intro z hz
      simpa only [mem_closedBall, Real.dist_eq] using hz.2)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const habs).inter (isOpen_lt habs continuous_const)
  have hCU : C ⊆ U := by
    intro z hz
    exact ⟨hδr.trans_le hz.1, hz.2.trans_lt (by linarith)⟩
  obtain ⟨v, hv, hvc, hvs, hvnear⟩ := exists_compactField_extension hC hU hCU
    (fun z : ℝ => c - z) (contDiff_const.sub contDiff_id).contDiffOn
  have hag : EqOn v (fun z => c - z) C := fun _ hz => subset_of_mem_nhdsSet hvnear hz
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds v hv hvc
  have haff (z : ℝ) (hzd : d ≤ |z - c|) (hzR : |z - c| ≤ R) :
      boundedFlow v hK hL z T = c + k * (z - c) := by
    have hlower : r ≤ Real.exp (-T) * |z - c| := by
      rw [hexp]
      exact hrkd.trans (mul_le_mul_of_nonneg_left hzd hk.le)
    have hupper : |z - c| ≤ 2 * R := hzR.trans (by linarith)
    simpa only [hexp] using
      boundedFlow_eq_scalar_contraction v hK hL c r (2 * R) z hT hlower hupper hag
  refine ⟨v, hv, hvc, K, L, hK, hL, T, δ, hT, hδ, ?_, haff, ?_⟩
  · intro t z hz
    apply boundedFlow_eq_self v hK hL z
    apply image_eq_zero_of_notMem_tsupport
    intro hzs
    exact (not_lt_of_ge hz) (hvs hzs).1
  · intro z hz
    have hlabs : |c - R - c| = R := by
      calc
        |c - R - c| = |-R| := by congr 1; ring
        _ = R := by rw [abs_neg, abs_of_pos hR]
    have huabs : |c + R - c| = R := by
      rw [add_sub_cancel_left, abs_of_pos hR]
    have hl := haff (c - R) (by rw [hlabs]; exact hdR) (by rw [hlabs])
    have hu := haff (c + R) (by rw [huabs]; exact hdR) (by rw [huabs])
    have hmono := (boundedFlow_strictMono v hK hL hv hvc T).monotone
    have hzl : c - R ≤ z := by linarith [(abs_le.mp hz).1]
    have hzu : z ≤ c + R := by linarith [(abs_le.mp hz).2]
    have hflowl : boundedFlow v hK hL (c - R) T ≤ boundedFlow v hK hL z T := hmono hzl
    have hflowu : boundedFlow v hK hL z T ≤ boundedFlow v hK hL (c + R) T := hmono hzu
    rw [hl] at hflowl
    rw [hu] at hflowu
    apply abs_le.mpr
    constructor <;> nlinarith

end PoincareConjecture.M25.Topology3D
