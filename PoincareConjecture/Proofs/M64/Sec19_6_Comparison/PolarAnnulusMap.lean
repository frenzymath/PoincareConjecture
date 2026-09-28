import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PeriodicRectangleLipschitz
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularLengthMap
import PoincareConjecture.Proofs.M60.Mathlib.CompactExtendedLipschitz
import Mathlib.Analysis.Calculus.ContDiff.WithLp












set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff NNReal ENNReal

namespace PoincareConjecture




noncomputable def m64PolarAnnulusMap {Y : Type*} (f : LoopPlane → Y)
    (z : LoopPlane) : Y :=
  f (annulusPoint (m60PlaneAngle z) (2 * ‖z‖ - 1))




theorem m64PolarAnnulusMap_eq_polar
    {Y : Type*} {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {z : LoopPlane} (hz : z ≠ 0) {theta : ℝ}
    (htheta : ‖z‖ • Proofs.M58.angularPoint theta = z) :
    m64PolarAnnulusMap f z = f (annulusPoint theta (2 * ‖z‖ - 1)) := by
  have heq : Proofs.M58.angularPoint (m60PlaneAngle z) =
      Proofs.M58.angularPoint theta := by
    have h := congrArg (fun w : LoopPlane => ‖z‖⁻¹ • w)
      ((m60PlaneAngle_polar z).trans htheta.symm)
    simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul] using h
  exact m60Periodic_eq_of_angularPoint_eq
    (show Function.Periodic (fun x => f (annulusPoint x (2 * ‖z‖ - 1))) rampPeriod from
      fun x => hperiodic x _) heq




theorem m64_periodic_rectangle_representative
    {Y : Type*} {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (x : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ p ∈ m64AnnulusDomain, f p = f (annulusPoint x s) := by
  let k : ℤ := Int.floor (x / curvePeriod)
  let y : ℝ := x - (k : ℝ) * curvePeriod
  have hy : y ∈ Icc (0 : ℝ) curvePeriod := by
    have h0 := (le_div_iff₀ Real.two_pi_pos).mp (Int.floor_le (x / curvePeriod))
    have h1 := (div_lt_iff₀ Real.two_pi_pos).mp (Int.lt_floor_add_one (x / curvePeriod))
    dsimp only [y, k, curvePeriod] at h0 h1 ⊢
    constructor <;> nlinarith only [h0, h1]
  refine ⟨annulusPoint y s, ⟨hy.1, hy.2, hs⟩, ?_⟩
  have hp : Function.Periodic (fun t => f (annulusPoint t s)) curvePeriod :=
    fun t => hperiodic t s
  have h := hp.int_mul k y
  simpa only [y, sub_add_cancel] using h.symm




theorem m64PolarAnnulusMap_polar
    {Y : Type*} {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {r : ℝ} (hr : 0 < r) (theta : ℝ) :
    m64PolarAnnulusMap f (r • Proofs.M58.angularPoint theta) =
      f (annulusPoint theta (2 * r - 1)) := by
  have hnorm : ‖r • Proofs.M58.angularPoint theta‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Proofs.M58.norm_angularPoint, mul_one]
  have hn : r • Proofs.M58.angularPoint theta ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact hr)
  have h := m64PolarAnnulusMap_eq_polar hperiodic hn
    (theta := theta) (by rw [hnorm])
  simpa only [hnorm] using h




theorem m64PolarAnnulusMap_lipschitz
    {Y : Type*} [PseudoEMetricSpace Y] {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {K : ℝ≥0} (hLip : LipschitzOnWith K f m64AnnulusDomain) :
    ∃ L : ℝ≥0, LipschitzOnWith L (m64PolarAnnulusMap f)
      {z : LoopPlane | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
  let Q : Set LoopPlane := {z | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1}
  let T : Set LoopPlane := {p | 0 ≤ p 1 ∧ p 1 ≤ 1}
  have hQ : IsCompact Q := by
    have heq : Q = closedBall (0 : LoopPlane) 1 ∩ {z : LoopPlane | 1 / 2 ≤ ‖z‖} := by
      ext z
      simp only [Q, mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact and_comm
    rw [heq]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hnonzero {z : LoopPlane} (hz : z ∈ Q) : z ≠ 0 :=
    norm_pos_iff.mp (by linarith [hz.1])
  have hstrip := m64_periodic_rectangle_locally_lipschitz hperiodic hLip
  apply M60.exists_lipschitzOnWith_of_compact_edist_ne_top hQ
  · intro z hz
    obtain ⟨theta, htheta, hpolar⟩ := m60_exists_contDiffAt_planeAngle (hnonzero hz)
    let chi : LoopPlane → LoopPlane := fun w => annulusPoint (theta w) (2 * ‖w‖ - 1)
    have hchi : ContDiffAt ℝ 1 chi z := by
      apply (contDiffAt_piLp 2).mpr
      intro i
      fin_cases i
      · exact htheta
      · exact (contDiffAt_const.mul (contDiffAt_norm ℝ (hnonzero hz))).sub contDiffAt_const
    have hmaps : MapsTo chi Q T := by
      intro w hw
      change 0 ≤ 2 * ‖w‖ - 1 ∧ 2 * ‖w‖ - 1 ≤ 1
      constructor <;> linarith [hw.1, hw.2]
    obtain ⟨C, V, hV, hCV⟩ := hchi.exists_lipschitzOnWith
    obtain ⟨D, W, hW, hDW⟩ := hstrip (hmaps hz)
    have hpre : chi ⁻¹' W ∈ 𝓝[Q] z :=
      hchi.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps hW
    refine ⟨D * C, (V ∩ chi ⁻¹' W) ∩ Q,
      inter_mem (inter_mem (nhdsWithin_le_nhds hV) hpre) self_mem_nhdsWithin, ?_⟩
    have hcomp : LipschitzOnWith (D * C) (f ∘ chi) ((V ∩ chi ⁻¹' W) ∩ Q) :=
      hDW.comp (hCV.mono (fun _ hw => hw.1.1)) (fun _ hw => hw.1.2)
    intro x hx y hy
    rw [m64PolarAnnulusMap_eq_polar hperiodic (hnonzero hx.2) (hpolar x),
      m64PolarAnnulusMap_eq_polar hperiodic (hnonzero hy.2) (hpolar y)]
    exact hcomp hx hy
  · intro x hx y hy
    obtain ⟨p, hp, hep⟩ := m64_periodic_rectangle_representative hperiodic
      (m60PlaneAngle x) (s := 2 * ‖x‖ - 1)
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨q, hq, heq⟩ := m64_periodic_rectangle_representative hperiodic
      (m60PlaneAngle y) (s := 2 * ‖y‖ - 1)
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    change edist (f (annulusPoint (m60PlaneAngle x) (2 * ‖x‖ - 1)))
      (f (annulusPoint (m60PlaneAngle y) (2 * ‖y‖ - 1))) ≠ ⊤
    rw [← hep, ← heq]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top p q)) (hLip hp hq)

end PoincareConjecture
