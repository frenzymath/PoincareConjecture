import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_PhysicalBirthMetric
import PoincareConjecture.Proofs.M13.OrdinaryFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

open M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem seed_cap_birth_tangent_bounds
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J) (hbase : ∀ y ∈ U, HEq (e.forward 0 hzero y) y)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hetahalf : eta ≤ 1 / 2)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A)
    (v : TangentSpace (𝓡 3) x) :
    let gQ : RiemannianMetric 3 (F.slice t).carrier :=
      M13.scaleSmoothMetric (F.metric t) ((F.parameters.h t)⁻¹ ^ 2)
        (sq_pos_of_pos (inv_pos.mpr hh))
    gQ.tangentNorm (initial.chart x) (mfderiv (𝓡 3) (𝓡 3) initial.chart x v) ≤
        2 * F.standard_initial.metric.tangentNorm x v ∧
      F.standard_initial.metric.tangentNorm x v ≤
        2 * gQ.tangentNorm (initial.chart x) (mfderiv (𝓡 3) (𝓡 3) initial.chart x v) := by
  let gQ : RiemannianMetric 3 (F.slice t).carrier :=
    M13.scaleSmoothMetric (F.metric t) ((F.parameters.h t)⁻¹ ^ 2)
      (sq_pos_of_pos (inv_pos.mpr hh))
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := himage ▸ (capInitialPartialDiffeomorph initial).open_target
  have hxU : initial.chart x ∈ U := himage ▸ mem_image_of_mem initial.chart hx
  have hcoeff : capComparisonCoefficients e initial.chart 0 hzero x v v =
      gQ.inner (initial.chart x) (mfderiv (𝓡 3) (𝓡 3) initial.chart x v)
        (mfderiv (𝓡 3) (𝓡 3) initial.chart x v) := by
    rw [capComparisonCoefficients_apply,
      surgeryCylinder_pullbackInner_zero hU e hzero hbase hxU]
    rfl
  obtain ⟨hl, hu⟩ := capComparison_metric_bounds e initial.chart comparison heta 0 hzero hx v
  have hmodel : S.metric 0 = F.standard_initial.metric := S.base.initial_metric
  rw [hmodel, hcoeff] at hl hu
  let B := F.standard_initial.metric.inner x v v
  let V := gQ.inner (initial.chart x) (mfderiv (𝓡 3) (𝓡 3) initial.chart x v)
    (mfderiv (𝓡 3) (𝓡 3) initial.chart x v)
  have hB : 0 ≤ B := by
    by_cases hv : v = 0
    · simp [B, hv]
    · exact (F.standard_initial.metric.pos x v hv).le
  have hV : 0 ≤ V := by
    dsimp only [V]
    by_cases hv : mfderiv (𝓡 3) (𝓡 3) initial.chart x v = 0
    · simp [hv]
    · exact (gQ.pos _ _ hv).le
  have hupper : V ≤ 4 * B := by
    change (1 - eta) * B ≤ V at hl
    change V ≤ (1 + eta) * B at hu
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - eta by linarith) hB]
  have hlower : B ≤ 4 * V := by
    change (1 - eta) * B ≤ V at hl
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - eta by linarith) hB]
  change Real.sqrt V ≤ 2 * Real.sqrt B ∧ Real.sqrt B ≤ 2 * Real.sqrt V
  constructor
  · apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [Real.sq_sqrt hB]⟩
  · apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [Real.sq_sqrt hV]⟩

end PoincareConjecture.Proofs.M47
