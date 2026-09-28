import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularAngles
import PoincareConjecture.Proofs.M60.Mathlib.LengthParameterHomotopy
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace PoincareConjecture

noncomputable def m60AnnularLengthMap {E : Type*} (beta : ℝ → E) (a b : ℝ → ℝ)
    (z : LoopPlane) : E :=
  beta (M60.lengthParameterInterpolation a b (2 * ‖z‖ - 1, m60PlaneAngle z))

theorem m60AnnularLengthMap_eq_polar {E : Type*} {beta : ℝ → E} {a b : ℝ → ℝ}
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, Function.Periodic
      (fun t => beta (M60.lengthParameterInterpolation a b (u, t))) rampPeriod)
    {z : LoopPlane} (hz : 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1) {t : ℝ}
    (ht : ‖z‖ • Proofs.M58.angularPoint t = z) :
    m60AnnularLengthMap beta a b z =
      beta (M60.lengthParameterInterpolation a b (2 * ‖z‖ - 1, t)) := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (by linarith [hz.1])
  have heq : Proofs.M58.angularPoint (m60PlaneAngle z) = Proofs.M58.angularPoint t := by
    have h := congrArg (fun w : LoopPlane => ‖z‖⁻¹ • w)
      ((m60PlaneAngle_polar z).trans ht.symm)
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using h
  exact m60Periodic_eq_of_angularPoint_eq
    (hp (2 * ‖z‖ - 1) ⟨by linarith [hz.1], by linarith [hz.2]⟩) heq

theorem m60AnnularLengthMap_traces {E : Type*} {beta : ℝ → E} {a b : ℝ → ℝ}
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, Function.Periodic
      (fun t => beta (M60.lengthParameterInterpolation a b (u, t))) rampPeriod) (t : ℝ) :
    m60AnnularLengthMap beta a b ((1 / 2 : ℝ) • Proofs.M58.angularPoint t) = beta (a t) ∧
      m60AnnularLengthMap beta a b (Proofs.M58.angularPoint t) = beta (b t) := by
  have hn : ‖(1 / 2 : ℝ) • Proofs.M58.angularPoint t‖ = 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      Proofs.M58.norm_angularPoint, mul_one]
  constructor
  · have h := m60AnnularLengthMap_eq_polar hp (z := (1 / 2 : ℝ) • Proofs.M58.angularPoint t)
      (by rw [hn]; norm_num) (by rw [hn])
    norm_num [hn, M60.lengthParameterInterpolation] at h
    exact h
  · have h := m60AnnularLengthMap_eq_polar hp (z := Proofs.M58.angularPoint t)
      (by rw [Proofs.M58.norm_angularPoint]; norm_num)
      (by rw [Proofs.M58.norm_angularPoint, one_smul])
    norm_num [Proofs.M58.norm_angularPoint, M60.lengthParameterInterpolation] at h
    exact h

theorem m60AnnularLengthMap_local_scalar {E : Type*} {beta : ℝ → E} {a b : ℝ → ℝ}
    {A B : ℝ≥0} (ha : LipschitzWith A a) (hb : LipschitzWith B b)
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, Function.Periodic
      (fun t => beta (M60.lengthParameterInterpolation a b (u, t))) rampPeriod)
    {z : LoopPlane} (hz : z ≠ 0) :
    ∃ (theta : LoopPlane → ℝ) (K : ℝ≥0) (U : Set LoopPlane), U ∈ 𝓝 z ∧
      LipschitzOnWith K (fun w =>
        M60.lengthParameterInterpolation a b (2 * ‖w‖ - 1, theta w)) U ∧
      ∀ w : LoopPlane, 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 →
        m60AnnularLengthMap beta a b w =
          beta (M60.lengthParameterInterpolation a b (2 * ‖w‖ - 1, theta w)) := by
  obtain ⟨theta, htheta, hpolar⟩ := m60_exists_contDiffAt_planeAngle hz
  let p : LoopPlane → ℝ × ℝ := fun w => (2 * ‖w‖ - 1, theta w)
  have hnorm : ContDiffAt ℝ 1 (norm : LoopPlane → ℝ) z := contDiffAt_norm ℝ hz
  have hpair : ContDiffAt ℝ 1 p z :=
    ((contDiffAt_const.mul hnorm).sub contDiffAt_const).prodMk htheta
  obtain ⟨C, V, hV, hCV⟩ := hpair.exists_lipschitzOnWith
  obtain ⟨D, W, hW, hDW⟩ := M60.locallyLipschitz_lengthParameterInterpolation ha hb (p z)
  refine ⟨theta, D * C, V ∩ p ⁻¹' W,
    inter_mem hV (hpair.continuousAt hW), ?_, ?_⟩
  · exact hDW.comp (hCV.mono inter_subset_left) (fun _ hx => hx.2)
  · intro w hw
    exact m60AnnularLengthMap_eq_polar hp hw (hpolar w)

end PoincareConjecture
