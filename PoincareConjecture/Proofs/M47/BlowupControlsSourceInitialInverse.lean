import PoincareConjecture.Proofs.M47.CanonicalNeckCapTipDistance










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem source_initial_inverse_tangent_bound
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta Lambda : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J) (hbase : ∀ y ∈ U, HEq (e.forward 0 hzero y) y)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hLambda : 0 < Lambda)
    (hbudget : 1 ≤ (1 - eta) * Lambda ^ 2)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A)
    (v : TangentSpace (𝓡 3) x) :
    F.standard_initial.metric.tangentNorm x v ≤ Lambda *
      RiemannianMetric.tangentNorm
        (M13.scaleSmoothMetric (F.metric t) ((F.parameters.h t)⁻¹ ^ 2)
          (sq_pos_of_pos (inv_pos.mpr hh)))
        (initial.chart x) (mfderiv (𝓡 3) (𝓡 3) initial.chart x v) := by
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
  have hl := (capComparison_metric_bounds e initial.chart comparison heta 0 hzero hx v).1
  have hmodel : S.metric 0 = F.standard_initial.metric := S.base.initial_metric
  rw [hmodel, hcoeff] at hl
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
  change (1 - eta) * B ≤ V at hl
  have hbound : B ≤ Lambda ^ 2 * V := by
    calc
      B ≤ ((1 - eta) * Lambda ^ 2) * B := by nlinarith [mul_le_mul_of_nonneg_right hbudget hB]
      _ = Lambda ^ 2 * ((1 - eta) * B) := by ring
      _ ≤ Lambda ^ 2 * V := mul_le_mul_of_nonneg_left hl (sq_nonneg _)
  change Real.sqrt B ≤ Lambda * Real.sqrt V
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hLambda.le (Real.sqrt_nonneg _), ?_⟩
  rw [mul_pow, Real.sq_sqrt hV]
  exact hbound



theorem source_initial_inverse_tip_distance
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta Lambda : ℝ}
    (hA : 0 < A) {J : Set ℝ}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
      ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (hbase : ∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
      HEq (e.forward 0 hzero y) y)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hLambda : 0 < Lambda)
    (hbudget : 1 ≤ (1 - eta) * Lambda ^ 2)
    {z : StandardCapSpace} (hz : z ∈ F.standard_initial.metric.ball 0 A) :
    (F.standard_initial.metric.edist 0 z).toReal ≤ Lambda * (F.parameters.h t)⁻¹ *
      ((F.metric t).edist ((F.event t hT).caps i).tip (initial.chart z)).toReal := by
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let gQ : RiemannianMetric 3 (F.slice t).carrier := M13.scaleSmoothMetric (F.metric t) Q hQ
  let q := capInitialPartialDiffeomorph initial
  have hsqrt : Real.sqrt Q = (F.parameters.h t)⁻¹ := Real.sqrt_sq (inv_pos.mpr hh).le
  have hball : gQ.ball (q 0) A =
      (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
    have hrad : Real.sqrt Q * (A * F.parameters.h t) = A := by
      rw [hsqrt]
      field_simp
    have h := M13.scaleSmoothMetric_ball (F.metric t) Q hQ (q 0) (A * F.parameters.h t)
    rw [hrad] at h
    exact h.trans (congrArg (fun x => (F.metric t).ball x (A * F.parameters.h t))
      initial.tip_eq)
  have hsource0 : (0 : StandardCapSpace) ∈ q.source := by
    change F.standard_initial.metric.edist 0 0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hA
  have hcover : gQ.ball (q 0) A ⊆ q.target := by
    rw [hball]
    change (F.metric t).ball _ _ ⊆ initial.chart '' F.standard_initial.metric.ball 0 A
    rw [comparison.choose_spec.2.2.2.1]
  have himage : q z ∈ gQ.ball (q 0) A := by
    rw [hball, ← comparison.choose_spec.2.2.2.1]
    exact mem_image_of_mem initial.chart hz
  have hbound (x : StandardCapSpace) (hx : x ∈ q.source)
      (v : TangentSpace (𝓡 3) x) :
      F.standard_initial.metric.tangentNorm x v ≤ Lambda *
        gQ.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x v) :=
    source_initial_inverse_tangent_bound e initial comparison hzero hbase hh heta
      hLambda hbudget hx v
  have hd := cap_inverse_toReal_edist_le F.standard_initial.metric gQ
    q.toOpenPartialHomeomorph (q.contMDiffOn_toFun.of_le (by simp))
    (q.contMDiffOn_invFun.of_le (by simp)) hsource0 hLambda hcover hbound hz himage
  have hscale := M13.homothety_edist (F.metric t) gQ
    (Diffeomorph.refl (𝓡 3) (F.slice t).carrier ∞) Q hQ
    (M13.identity_metricHomothety (F.metric t) Q hQ) (q 0) (q z)
  change gQ.edist (q.toOpenPartialHomeomorph 0) (q.toOpenPartialHomeomorph z) = _ at hscale
  rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hsqrt] at hd
  have htip : q 0 = ((F.event t hT).caps i).tip := initial.tip_eq
  rw [htip] at hd
  have hqz : q z = initial.chart z := rfl
  rw [hqz] at hd
  simpa only [mul_assoc] using hd

end PoincareConjecture.M47
