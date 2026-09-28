import PoincareConjecture.Proofs.M47.CanonicalNeckCapTipDistance
import PoincareConjecture.Proofs.M47.BlowupControlsCapTangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem source_initial_standard_tangent_le
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {s : ℝ} (hs : s ∈ Ico 0 standard.flow.base.lifetime)
    (x : StandardCapSpace) (v : TangentSpace (𝓡 3) x) :
    (standard.flow.metric s).tangentNorm x v ≤ g0.metric.tangentNorm x v := by
  have hsub : Icc 0 s ⊆ Ico 0 standard.flow.base.lifetime :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt hs.2⟩
  have hmono := standard.flow.base.flow.inner_self_antitoneOn_of_nonnegative_ricci
    (convex_Icc (0 : ℝ) s) hsub x v (fun t ht =>
      M04.nonneg_ricci_of_nonnegativeSectionalAt (standard.flow.connection t) x
        (standard.nonnegative_sectional t (hsub ht) x) v)
  have hinner := hmono ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
  change (standard.flow.metric s).inner x v v ≤ (standard.flow.metric 0).inner x v v at hinner
  have hinitial : standard.flow.metric 0 = g0.metric := standard.flow.base.initial_metric
  rw [hinitial] at hinner
  exact Real.sqrt_le_sqrt hinner

theorem source_initial_cap_chart_tangent_le
    {F : SurgeryFlowData.{u}} (standard : RepairedStandardCapExistenceData F.standard_initial)
    {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {A eta : ℝ} {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F standard.flow A eta e initial.chart)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000)
    (s : ℝ) (hs : s ∈ J) {x : StandardCapSpace}
    (hx : x ∈ F.standard_initial.metric.ball 0 A) (v : TangentSpace (𝓡 3) x) :
    let f := actualCapSliceChart e initial comparison s hs
    (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).tangentNorm
      (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        (2 * F.parameters.h t) * F.standard_initial.metric.tangentNorm x v := by
  let f := actualCapSliceChart e initial comparison s hs
  let g := F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))
  have hupper : eta ≤ (2 : ℝ) ^ 2 - 1 := by linarith only [hetaSmall]
  have hlower : eta ≤ 1 - (2 : ℝ)⁻¹ ^ 2 := by norm_num; linarith only [hetaSmall]
  have h := (actualCapSliceChart_tangent_bounds e initial comparison hh heta
    (by norm_num : (0 : ℝ) < 2) hupper hlower s hs hx v).1
  change RiemannianMetric.tangentNorm
      (M13.scaleSmoothMetric g ((F.parameters.h t)⁻¹ ^ 2)
        (sq_pos_of_pos (inv_pos.mpr hh))) (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ _ at h
  rw [M13.scaleSmoothMetric_tangentNorm,
    Real.sqrt_sq (inv_pos.mpr hh).le] at h
  have hmodel := source_initial_standard_tangent_le standard
    (comparison.choose_spec.2.2.1 s hs) x v
  have hbound := h.trans (mul_le_mul_of_nonneg_left hmodel (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only
  calc
    _ = F.parameters.h t * ((F.parameters.h t)⁻¹ *
        g.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    _ ≤ F.parameters.h t * (2 * F.standard_initial.metric.tangentNorm x v) :=
      mul_le_mul_of_nonneg_left hbound hh.le
    _ = _ := by ring

end PoincareConjecture.M47
