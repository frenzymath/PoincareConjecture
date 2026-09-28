import PoincareConjecture.Proofs.M09.HarnackIntegrability
import PoincareConjecture.Proofs.M09.ExponentialAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_harnack_integral_square_eq {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    reducedHarnackIntegral F T (A.gamma Z) (backwardScalarEvolutionAlong F T (A.gamma Z)) b =
      A.action Z b / 2 -
        ((Real.sqrt b) ^ 3 *
          (F.connection (T - (Real.sqrt b) ^ 2)).scalarCurvature (A.squareFamily Z (Real.sqrt b)) +
          Real.sqrt b * regularizedCurveEnergy F T (A.squareFamily Z) (Real.sqrt b) / 4) := by
  let U := ((fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain) ∩
    Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hU : IsOpen U := (A.square_open.preimage
    (continuous_const.prodMk continuous_id)).inter isOpen_Ioo
  have hKU : Set.Icc 0 (Real.sqrt b) ⊆ U := by
    intro s hs
    have hsmax := hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact ⟨A.square_contains ⟨Set.mem_univ _, hs.1, hsmax⟩,
      (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1, hsmax⟩
  have hα := (lExponentialFamily_squareSlice_contMDiffOn A Z).mono
    (show U ⊆ (fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain from Set.inter_subset_left)
  let S : ℝ → ℝ := fun s ↦ (F.connection (T - s ^ 2)).scalarCurvature (A.squareFamily Z s)
  let E := regularizedCurveEnergy F T (A.squareFamily Z)
  have hS : ContDiffOn ℝ ∞ S U :=
    ((squareTime_scalar_smooth F hM04 T τmax hτmax hwindow).comp
      (contMDiffOn_id.prodMk hα) (fun s hs ↦ ⟨hs.2, Set.mem_univ _⟩)).contDiffOn
  have hE : ContDiffOn ℝ ∞ E U := regularizedCurveEnergy_contDiffOn F T τmax hτmax hwindow
    (A.squareFamily Z) U hU hα Set.inter_subset_right
  let P : ℝ → ℝ := fun s ↦ s ^ 3 * S s + s * E s / 4
  let D : ℝ → ℝ := fun s ↦ 2 * s ^ 2 * S s + (1 / 2 : ℝ) * E s
  have hP : ContDiffOn ℝ ∞ P U :=
    ((contDiffOn_id.pow 3).mul hS).add ((contDiffOn_id.mul hE).div_const 4)
  have hD : ContDiffOn ℝ ∞ D U :=
    ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul hS).add (contDiffOn_const.mul hE)
  have hPi : IntervalIntegrable (deriv P) MeasureTheory.volume 0 (Real.sqrt b) :=
    ((hP.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn.mono hKU).intervalIntegrable_of_Icc
      (Real.sqrt_nonneg b)
  have hDi : IntervalIntegrable D MeasureTheory.volume 0 (Real.sqrt b) :=
    (hD.continuousOn.mono hKU).intervalIntegrable_of_Icc (Real.sqrt_nonneg b)
  have hFTC : (∫ s in 0..Real.sqrt b, deriv P s) = P (Real.sqrt b) - P 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hPi
    intro s hs
    have hs' : s ∈ Set.Icc 0 (Real.sqrt b) := by
      simpa only [Set.uIcc_of_le (Real.sqrt_nonneg b)] using hs
    exact ((hP.contDiffAt (hU.mem_nhds (hKU hs'))).differentiableAt (by simp)).hasDerivAt
  have hPder (s : ℝ) (hs : s ∈ Set.Ioo 0 (Real.sqrt b)) :
      deriv P s = 3 * s ^ 2 * S s + s ^ 3 * deriv S s +
        (E s + s * deriv E s) / 4 := by
    have hSd := ((hS.contDiffAt (hU.mem_nhds (hKU (Set.Ioo_subset_Icc_self hs)))).differentiableAt
      (by simp)).hasDerivAt
    have hEd := ((hE.contDiffAt (hU.mem_nhds (hKU (Set.Ioo_subset_Icc_self hs)))).differentiableAt
      (by simp)).hasDerivAt
    convert! (((hasDerivAt_pow 3 s).mul hSd).add
      (((hasDerivAt_id s).mul hEd).div_const 4)).deriv using 1 <;>
      simp only [P, Nat.cast_ofNat, Nat.reduceSub, one_mul, id_eq]
  have hsq : ∀ s ∈ Set.Ioo (min 0 (Real.sqrt b)) (max 0 (Real.sqrt b)),
      HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    intro s _
    simpa using hasDerivAt_pow 2 s
  have hpos : ∀ s ∈ Set.Ioo (min 0 (Real.sqrt b)) (max 0 (Real.sqrt b)), 0 ≤ 2 * s := by
    intro s hs
    have hs' : 0 < s := by simpa only [min_eq_left (Real.sqrt_nonneg b)] using hs.1
    positivity
  let H := reducedHarnackDensity F T (A.gamma Z) (backwardScalarEvolutionAlong F T (A.gamma Z))
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s) (g := fun t ↦ t * Real.sqrt t * H t)
    (continuous_pow 2).continuousOn hsq hpos
  simp only [zero_pow two_ne_zero, Real.sq_sqrt hb.le] at hchange
  have haction : (∫ s in 0..Real.sqrt b, D s) = A.action Z b :=
    (lExponentialFamily_action_square_eq A Z b hb hmax).symm
  change (∫ t in 0..b, t * Real.sqrt t * H t) = A.action Z b / 2 - P (Real.sqrt b)
  rw [← hchange]
  calc
    (∫ s in 0..Real.sqrt b, (s ^ 2 * Real.sqrt (s ^ 2) * H (s ^ 2)) * (2 * s)) =
        ∫ s in 0..Real.sqrt b, (D s / 2 - deriv P s) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_nonneg b)
      intro s hs
      dsimp only
      rw [Real.sqrt_sq hs.1.le, hPder s hs,
        lExponentialFamily_weightedHarnack_square hM04 hτmax hwindow A Z b hb hmax s hs]
      dsimp only [D, S, E]
      ring
    _ = A.action Z b / 2 - P (Real.sqrt b) := by
      rw [intervalIntegral.integral_sub (hDi.div_const 2) hPi,
        intervalIntegral.integral_div, haction, hFTC]
      simp only [P, zero_pow (by norm_num : 3 ≠ 0), zero_mul, zero_div, add_zero, sub_zero]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_harnack_integral_eq {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    reducedHarnackIntegral F T (A.gamma Z) (backwardScalarEvolutionAlong F T (A.gamma Z)) b =
      A.action Z b / 2 - b * Real.sqrt b *
        ((F.connection (T - b)).scalarCurvature (A.gamma Z b) +
          (F.metric (T - b)).inner (A.gamma Z b)
            (curveVelocity (A.gamma Z) b) (curveVelocity (A.gamma Z) b)) := by
  have hs : Real.sqrt b ∈ Set.Ioo 0 (Real.sqrt τmax) :=
    ⟨Real.sqrt_pos.mpr hb, Real.sqrt_lt_sqrt hb.le hmax⟩
  have hbase := A.square_agrees Z (Real.sqrt b) ⟨hs.1.le, hs.2⟩
  have hvel0 := lExponentialFamily_square_velocity_eq A Z (Real.sqrt b) hs
  have hvsq := congrArg (fun t : ℝ ↦
    (curveVelocity (A.gamma Z) t : EuclideanSpace ℝ (Fin n))) (Real.sq_sqrt hb.le)
  have hvel : (curveVelocity (A.squareFamily Z) (Real.sqrt b) : EuclideanSpace ℝ (Fin n)) =
      (2 * Real.sqrt b) • curveVelocity (A.gamma Z) b :=
    hvel0.trans (congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ (2 * Real.sqrt b) • v) hvsq)
  simp only [Real.sq_sqrt hb.le] at hbase
  rw [lExponentialFamily_harnack_integral_square_eq hM04 hτmax hwindow A Z b hb hmax]
  unfold regularizedCurveEnergy
  rw [Real.sq_sqrt hb.le, hbase, hvel]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hcube : Real.sqrt b ^ 3 = b * Real.sqrt b := by rw [pow_succ, Real.sq_sqrt hb.le]
  ring_nf
  rw [hcube]
  ring

end PoincareConjecture.Proofs.M09
