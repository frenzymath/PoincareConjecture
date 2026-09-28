import PoincareConjecture.Proofs.M14.Sec6_2_CurveVelocity
import PoincareConjecture.Proofs.M08.SquareEnergy
import PoincareConjecture.Statements.M12GeneralizedEquation
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}



noncomputable def squareCurveDensity (G : GeneralizedLGeometryTransport n X time I)
    (α : ℝ → G.Point) (J : Set ℝ) (s : ℝ) : ℝ :=
  2 * s ^ 2 * horizontalScalarCurvature G.leafwise (α s) +
    (1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (α s)
      (projectedCurveVelocityWithin G α J s) (projectedCurveVelocityWithin G α J s)

variable {G : GeneralizedLGeometryTransport n X time I} {α : ℝ → G.Point} {J : Set ℝ}



theorem squareCurveDensity_contDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hJ : UniqueDiffOn ℝ J) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α J) :
    ContDiffOn ℝ ∞ (squareCurveDensity G α J) J := by
  have hA := projectedCurveVelocityWithin_smooth (G := G) hJ hα
  have hmetric := G.spacetime.horizontalMetric.contMDiff.comp_contMDiffOn hα
  have hpair := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial G.Point ℝ) hA hA
  have hg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun s => G.spacetime.horizontalMetric.inner (α s)
        (projectedCurveVelocityWithin G α J s) (projectedCurveVelocityWithin G α J s)) J := by
    intro s hs
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
      using (Bundle.contMDiffWithinAt_totalSpace.mp (hpair s hs)).2
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar := (H.scalar_smooth.comp_contMDiffOn hα).contDiffOn
  exact ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul hscalar).add
    (contDiffOn_const.mul hg.contDiffOn)



theorem sqrtPullback_contMDiffOn {a b : ℝ} (ha : 0 ≤ a)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b)) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun τ => α (Real.sqrt τ)) (Ioo a b) := by
  intro τ hτ
  have hτ0 : 0 < τ := ha.trans_lt hτ.1
  have hs : Real.sqrt τ ∈ Ioo (Real.sqrt a) (Real.sqrt b) :=
    ⟨Real.sqrt_lt_sqrt ha hτ.1, Real.sqrt_lt_sqrt hτ0.le hτ.2⟩
  have hα' := (hα _ (Ioo_subset_Icc_self hs)).contMDiffAt (Icc_mem_nhds hs.1 hs.2)
  exact (hα'.comp τ (Real.contDiffAt_sqrt (ne_of_gt hτ0)).contMDiffAt).contMDiffWithinAt



theorem projectedVelocity_sqrtPullback {a b s : ℝ} (ha : 0 ≤ a)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b))
    (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b)) :
    (projectedCurveVelocityWithin G α (M14SqrtParameterInterval a b) s).val =
      (2 * s) • (projectedCurveVelocity G (fun τ => α (Real.sqrt τ)) (s ^ 2)).val := by
  let β : ℝ → G.Point := fun τ => α (Real.sqrt τ)
  have hs0 : 0 < s := (Real.sqrt_nonneg a).trans_lt hs.1
  have hτ : s ^ 2 ∈ Ioo a b :=
    ⟨Real.lt_sq_of_sqrt_lt hs.1, (Real.lt_sqrt hs0.le).mp hs.2⟩
  have hβ := ((sqrtPullback_contMDiffOn ha hα _ hτ).contMDiffAt
    (isOpen_Ioo.mem_nhds hτ)).mdifferentiableAt (by simp)
  have hnear : α =ᶠ[𝓝 s] fun r => β (r ^ 2) := by
    filter_upwards [Ioi_mem_nhds hs0] with r hr
    simp only [β, Real.sqrt_sq hr.le]
  have hg := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1)
    (hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n))
  have hw := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1)
    (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
      (f := α) (Icc_mem_nhds hs.1 hs.2))
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hsqmf : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (2 * s) • (1 : TangentSpace (𝓘(ℝ, ℝ)) (s ^ 2)) := by
    have hm := hsq.hasFDerivAt.hasMFDerivAt.mfderiv
    have hv := congrArg (fun L : TangentSpace (𝓘(ℝ, ℝ)) s →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ)) (s ^ 2) => L 1) hm
    change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * s)) (1 : ℝ) at hv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul, mul_one, one_mul]
      using hv
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ => r ^ 2) (g := β)
    hβ hsq.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hsqmf, map_smul] at hchain
  have htan := hw.trans (hg.trans hchain)
  have hp := congrArg (fun v : SpacetimeModelVector n =>
    (G.spacetime.horizontalProjection (α s) v).val) htan
  let v : SpacetimeModelVector n := mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) β (s ^ 2) 1
  have hb : α s = β (s ^ 2) := by simp only [β, Real.sqrt_sq hs0.le]
  calc
    _ = (G.spacetime.horizontalProjection (α s) ((2 * s) • v)).val := hp
    _ = (2 * s) • (G.spacetime.horizontalProjection (α s) v).val := by
      rw [map_smul]
      rfl
    _ = (2 * s) • (G.spacetime.horizontalProjection (β (s ^ 2)) v).val :=
      congrArg (fun w : SpacetimeModelVector n => (2 * s) • w)
        (congrArg (fun q : G.Point => (G.spacetime.horizontalProjection q v).val) hb)

private theorem inner_smul_of_val_eq {q r : G.Point} (h : q = r)
    {A : G.Horizontal q} {B : G.Horizontal r} {c : ℝ} (hv : A.val = c • B.val) :
    G.spacetime.horizontalMetric.inner q A A =
      c ^ 2 * G.spacetime.horizontalMetric.inner r B B := by
  cases h
  have hAB : A = c • B := Subtype.ext hv
  rw [hAB]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring



theorem squareCurveDensity_eq_transformed {a b s : ℝ} (ha : 0 ≤ a)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b))
    (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b)) :
    squareCurveDensity G α (M14SqrtParameterInterval a b) s =
      M14RawLIntegrand G (fun τ => α (Real.sqrt τ))
        (projectedCurveVelocity G (fun τ => α (Real.sqrt τ))) (s ^ 2) * (2 * s) := by
  have hs0 : 0 < s := (Real.sqrt_nonneg a).trans_lt hs.1
  have hvel := projectedVelocity_sqrtPullback (G := G) ha hα hs
  have hbase : α (Real.sqrt (s ^ 2)) = α s := by rw [Real.sqrt_sq hs0.le]
  have hpair : G.spacetime.horizontalMetric.inner (α s)
      (projectedCurveVelocityWithin G α (M14SqrtParameterInterval a b) s)
      (projectedCurveVelocityWithin G α (M14SqrtParameterInterval a b) s) =
    (2 * s) ^ 2 * G.spacetime.horizontalMetric.inner (α (Real.sqrt (s ^ 2)))
      (projectedCurveVelocity G (fun τ => α (Real.sqrt τ)) (s ^ 2))
      (projectedCurveVelocity G (fun τ => α (Real.sqrt τ)) (s ^ 2)) :=
    inner_smul_of_val_eq hbase.symm hvel
  unfold squareCurveDensity M14RawLIntegrand
  rw [hpair, congrArg (horizontalScalarCurvature G.leafwise) hbase.symm]
  let kin := G.spacetime.horizontalMetric.inner (α (Real.sqrt (s ^ 2)))
    (projectedCurveVelocity G (fun τ => α (Real.sqrt τ)) (s ^ 2))
    (projectedCurveVelocity G (fun τ => α (Real.sqrt τ)) (s ^ 2))
  let pot := horizontalScalarCurvature G.leafwise (α (Real.sqrt (s ^ 2)))
  change 2 * s ^ 2 * pot + (1 / 2 : ℝ) * ((2 * s) ^ 2 * kin) =
    Real.sqrt (s ^ 2) * (pot + kin) * (2 * s)
  rw [Real.sqrt_sq hs0.le]
  ring



theorem sqrtPullback_action_integrable (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b)) :
    IntervalIntegrable (M14RawLIntegrand G (fun τ => α (Real.sqrt τ))
      (projectedCurveVelocity G (fun τ => α (Real.sqrt τ)))) MeasureTheory.volume a b := by
  have hsqrt : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha hab
  have hdensity := (squareCurveDensity_contDiffOn hM12 (uniqueDiffOn_Icc hsqrt) hα).continuousOn
  exact M08.intervalIntegrable_of_square_transform ha hab.le
    (hdensity.intervalIntegrable_of_Icc hsqrt.le)
    (fun _ hs => squareCurveDensity_eq_transformed ha hα hs)

end PoincareConjecture.M14
