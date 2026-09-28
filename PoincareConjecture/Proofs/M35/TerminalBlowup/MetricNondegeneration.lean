import PoincareConjecture.Proofs.M35.TerminalBlowup.RicciTrace
import PoincareConjecture.Proofs.M35.Prop12_31.ScalarFloor
import PoincareConjecture.Proofs.M35.Prop12_31.ScalarPositivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

theorem metric_lower_at_of_nonnegative_sectional_and_scalar_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] {J : Set ℝ} (F : RicciFlow n M J) {s t K : ℝ}
    (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t) (x : M)
    (hsec : ∀ u ∈ Icc s t, ∀ v w : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection u).curvatureTensor x v w v w)
    (hscalar : ∀ u ∈ Icc s t, (F.connection u).scalarCurvature x ≤ K)
    (v : TangentSpace (𝓡 n) x) :
    Real.exp (-2 * K * (t - s)) * (F.metric s).inner x v v ≤
      (F.metric t).inner x v v := by
  let q (u : ℝ) := (F.metric u).inner x v v
  let f (u : ℝ) := Real.exp (2 * K * (u - s)) * q u
  have hJ : Icc s t ⊆ J := F.interval.out hs ht
  have hq (u : ℝ) : 0 ≤ q u := by
    by_cases hv : v = 0
    · simp [q, hv]
    · exact ((F.metric u).pos x v hv).le
  have hderiv (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivWithinAt f
        (Real.exp (2 * K * (u - s)) *
          (2 * K * q u - 2 * (F.connection u).ricci x v v)) (Icc s t) u := by
    convert! ((((hasDerivAt_id u).sub_const s).const_mul (2 * K)).exp.hasDerivWithinAt.mul
      ((F.equation u (hJ hu) x v v).mono hJ)) using 1
    dsimp only [f, q, id, Pi.neg_apply]
    ring
  have hmono : MonotoneOn f (Icc s t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t)
      (fun u hu => (hderiv u hu).continuousWithinAt)
      (fun u hu => (hderiv u (interior_subset hu)).mono interior_subset)
    intro u hu
    apply mul_nonneg (Real.exp_pos _).le
    have hRic := (F.connection u).ricci_le_scalar_mul_inner_of_nonnegative_sectional
      x (hsec u (interior_subset hu)) v
    have hbound := mul_le_mul_of_nonneg_right (hscalar u (interior_subset hu)) (hq u)
    change (F.connection u).ricci x v v ≤ (F.connection u).scalarCurvature x * q u at hRic
    linarith
  have h := hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simp only [f, sub_self, mul_zero, Real.exp_zero, one_mul] at h
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-2 * K * (t - s))).le
  have hcancel : Real.exp (-2 * K * (t - s)) * Real.exp (2 * K * (t - s)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  rwa [← mul_assoc, hcancel, one_mul] at hmul

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.RepairedStandardCapExistenceData

theorem exists_final_scalar_bound_of_not_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (x : StandardCapSpace)
    (hnot : ¬ Tendsto (fun t => (E.flow.connection t).scalarCurvature x)
      (𝓝[<] 1) atTop) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ico (1 / 2 : ℝ) 1,
      (E.flow.connection t).scalarCurvature x ≤ K := by
  by_contra hbounded
  push Not at hbounded
  apply hnot
  apply tendsto_atTop.2
  intro B
  obtain ⟨s, hs, hRs⟩ := hbounded (2 * (max B 0 + 1)) (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hs.2).filter_mono nhdsWithin_le_nhds] with t ht hst
  have hs0 : 0 < s := by linarith [hs.1]
  have hscalar := E.time_mul_scalar_le P hs0 hst ht x
  have htmem : t ∈ Ico 0 E.flow.base.lifetime := by
    exact ⟨hs0.le.trans hst.le, E.lifetime_one.symm ▸ ht⟩
  have htpos := E.scalar_pos htmem x
  have hspos : 0 < (E.flow.connection s).scalarCurvature x := by
    linarith [le_max_right B 0]
  have hlower : max B 0 + 1 < (E.flow.connection s).scalarCurvature x * s := by
    nlinarith [mul_nonneg hspos.le (sub_nonneg.mpr hs.1)]
  have hupper : (E.flow.connection t).scalarCurvature x * t ≤
      (E.flow.connection t).scalarCurvature x :=
    mul_le_of_le_one_right htpos.le ht.le
  linarith [le_max_left B 0]

theorem exists_metric_lower_of_not_scalar_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (x : StandardCapSpace)
    (hnot : ¬ Tendsto (fun t => (E.flow.connection t).scalarCurvature x)
      (𝓝[<] 1) atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Ico (1 / 2 : ℝ) 1,
      ∀ v : TangentSpace (𝓡 3) x,
        c * (E.flow.metric (1 / 2)).inner x v v ≤ (E.flow.metric t).inner x v v := by
  obtain ⟨K, hK, hbound⟩ := E.exists_final_scalar_bound_of_not_tendsto P x hnot
  refine ⟨Real.exp (-K), Real.exp_pos _, ?_⟩
  intro t ht v
  have hhalf : (1 / 2 : ℝ) ∈ Ico 0 E.flow.base.lifetime := by
    rw [E.lifetime_one]
    norm_num
  have htmem : t ∈ Ico 0 E.flow.base.lifetime :=
    ⟨(by linarith [ht.1]), E.lifetime_one.symm ▸ ht.2⟩
  have h := E.flow.base.flow.metric_lower_at_of_nonnegative_sectional_and_scalar_bound
    hhalf htmem ht.1 x
    (fun u hu => E.nonnegative_sectional u
      ⟨by linarith [hu.1], hu.2.trans_lt htmem.2⟩ x)
    (fun u hu => hbound u ⟨hu.1, hu.2.trans_lt ht.2⟩) v
  have hexp : Real.exp (-K) ≤ Real.exp (-2 * K * (t - 1 / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr ht.2.le)]
  have hv : 0 ≤ (E.flow.metric (1 / 2)).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((E.flow.metric (1 / 2)).pos x v hv).le
  exact (mul_le_mul_of_nonneg_right hexp hv).trans h

theorem scalar_tendsto_of_tangent_metric_tendsto_zero
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (x : StandardCapSpace)
    (v : TangentSpace (𝓡 3) x) (hv : v ≠ 0)
    (hzero : Tendsto (fun t => (E.flow.metric t).inner x v v) (𝓝[<] 1) (𝓝 0)) :
    Tendsto (fun t => (E.flow.connection t).scalarCurvature x) (𝓝[<] 1) atTop := by
  by_contra hnot
  obtain ⟨c, hc, hlower⟩ := E.exists_metric_lower_of_not_scalar_tendsto P x hnot
  have hle : c * (E.flow.metric (1 / 2)).inner x v v ≤ 0 := by
    apply ge_of_tendsto hzero
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with t ht hhalf
    exact hlower t ⟨hhalf.le, ht⟩ v
  exact (not_lt_of_ge hle) (mul_pos hc ((E.flow.metric (1 / 2)).pos x v hv))

end PoincareConjecture.RepairedStandardCapExistenceData
