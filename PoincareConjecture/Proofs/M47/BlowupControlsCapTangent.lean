import PoincareConjecture.Proofs.M47.BlowupControlsCapSliceMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46

local notation "E" => StandardCapSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem cap_sqrt_quadratic_comparison {A B eta Lambda : ℝ}
    (hB : 0 ≤ B) (hLambda : 0 < Lambda)
    (hlower : (1 - eta) * B ≤ A) (hupper : A ≤ (1 + eta) * B)
    (hetaUpper : eta ≤ Lambda ^ 2 - 1)
    (hetaLower : eta ≤ 1 - Lambda⁻¹ ^ 2) :
    Real.sqrt A ≤ Lambda * Real.sqrt B ∧ Real.sqrt B ≤ Lambda * Real.sqrt A := by
  have hnonnegative : 0 ≤ 1 - eta := by nlinarith [sq_nonneg Lambda⁻¹]
  have hA : 0 ≤ A := (mul_nonneg hnonnegative hB).trans hlower
  have hcancel : Lambda ^ 2 * Lambda⁻¹ ^ 2 = 1 := by field_simp [hLambda.ne']
  have hfactor : 1 ≤ Lambda ^ 2 * (1 - eta) := by
    have h := mul_le_mul_of_nonneg_left hetaLower (sq_nonneg Lambda)
    nlinarith
  have hforward : A ≤ Lambda ^ 2 * B :=
    hupper.trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  have hbackward : B ≤ Lambda ^ 2 * A := by
    calc
      B = 1 * B := by ring
      _ ≤ (Lambda ^ 2 * (1 - eta)) * B := mul_le_mul_of_nonneg_right hfactor hB
      _ = Lambda ^ 2 * ((1 - eta) * B) := by ring
      _ ≤ Lambda ^ 2 * A := mul_le_mul_of_nonneg_left hlower (sq_nonneg Lambda)
  constructor
  · apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hLambda.le (Real.sqrt_nonneg B), ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hB] using hforward
  · apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hLambda.le (Real.sqrt_nonneg A), ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hA] using hbackward

theorem actualCapSliceChart_tangent_bounds
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
    {S : MaximalStandardCapFlow F.standard_initial} {eta Lambda : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hLambda : 0 < Lambda)
    (hetaUpper : eta ≤ Lambda ^ 2 - 1)
    (hetaLower : eta ≤ 1 - Lambda⁻¹ ^ 2) (s : ℝ) (hs : s ∈ J)
    {x : E} (hx : x ∈ F.standard_initial.metric.ball 0 A) (v : E) :
    let q := actualCapSliceChart e initial comparison s hs
    let g' := m01RescaledMetric (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2)))
      ((F.parameters.h t)⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr hh))
    g'.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x v) ≤
        Lambda * (S.metric s).tangentNorm x v ∧
      (S.metric s).tangentNorm x v ≤
        Lambda * g'.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x v) := by
  have hB : 0 ≤ (S.metric s).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((S.metric s).pos x v hv).le
  obtain ⟨hlower, hupper⟩ := capComparison_metric_bounds e initial.chart comparison heta s hs hx v
  have h := cap_sqrt_quadratic_comparison hB hLambda hlower hupper hetaUpper hetaLower
  simpa only [RiemannianMetric.tangentNorm,
    actualCapSliceChart_metric e initial comparison s hs hh hx v v] using h

end PoincareConjecture.M47
