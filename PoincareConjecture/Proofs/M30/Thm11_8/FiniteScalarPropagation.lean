import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedScalarConvergence
import PoincareConjecture.Proofs.M30.Generalized.ScalarAlong
import PoincareConjecture.Proofs.M30.Generalized.Restriction
import PoincareConjecture.Proofs.M30.Mathlib.GuardedScalarComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem generalized_limit_scalar_le_double
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    {epsilon canonicalConstant kappa r0 mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r0 mu)
    (G : GeneralizedBlowupConvergence S J)
    {a b D : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (hIJ : Icc a b ⊆ J) (hD : 4 ≤ D)
    (htime : 8 * H.analytic_constant * D * (b - a) ≤ 1)
    (x : G.limit.carrier.carrier)
    (hinitial : (G.limit.flow.connection a).scalarCurvature x < D) :
    (G.limit.flow.connection b).scalarCurvature x ≤ 2 * D := by
  classical
  by_contra hbound
  have hlarge : 2 * D < (G.limit.flow.connection b).scalarCurvature x :=
    lt_of_not_ge hbound
  let eta := min ((D - (G.limit.flow.connection a).scalarCurvature x) / 2)
    (((G.limit.flow.connection b).scalarCurvature x - 2 * D) / 2)
  have heta : 0 < eta := lt_min (half_pos (sub_pos.mpr hinitial))
    (half_pos (sub_pos.mpr hlarge))
  obtain ⟨k, hk⟩ := (eventually_generalized_scalar_error G isCompact_Icc hIJ
    (isCompact_singleton (x := x)) heta).exists
  let e := Cylinder.restrict (G.embedding k) hk.1 Subset.rfl
  let Q := S.scale (G.subsequence k)
  have hQ : 0 < Q := S.base_scalar_pos (G.subsequence k)
  let f : ℝ → ℝ := Cylinder.scalarAlong e x
  have hx : x ∈ G.exhaustion.space k := hk.2.1 (mem_singleton x)
  have hchoice (s : ℝ) : ∃ d : ℝ, s ∈ Icc a b →
      HasDerivWithinAt f d (Icc a b) s ∧
        (4 * Q ≤ f s → |d| ≤ H.analytic_constant / Q * f s ^ 2) := by
    by_cases hs : s ∈ Icc a b
    · obtain ⟨d, hd, hrate⟩ := Cylinder.exists_scalarAlong_deriv_bound hC H e
        hs (hs.2.trans hb) x hx
      exact ⟨d, fun _ => ⟨hd, hrate⟩⟩
    · exact ⟨0, fun hs' => (hs hs').elim⟩
  choose d hd using hchoice
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hfa : f a ≤ D * Q := by
    have herr := (abs_lt.mp (hk.2.2 a haI (hk.1 haI) x (mem_singleton x))).2
    have hetaLe := min_le_left
      ((D - (G.limit.flow.connection a).scalarCurvature x) / 2)
      (((G.limit.flow.connection b).scalarCurvature x - 2 * D) / 2)
    apply (div_le_iff₀ hQ).mp
    dsimp only [f]
    rw [Cylinder.scalarAlong_of_mem e x haI]
    change (S.flow (G.subsequence k)).scalar
      ((G.embedding k).pointMap a (hk.1 haI) x) / Q ≤ D
    dsimp only [eta] at herr
    dsimp only [Q]
    linarith
  have htime' : 8 * (H.analytic_constant / Q) * (D * Q) * (b - a) ≤ 1 := by
    convert htime using 1
    field_simp [hQ.ne']
  have hDpos : 0 < D := by linarith
  have hfb := le_two_mul_of_deriv_le_sq_above
    (div_pos H.analytic_constant_pos hQ) (mul_pos hDpos hQ)
    (mul_le_mul_of_nonneg_right hD hQ.le)
    (fun s hs => (hd s hs).1.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).1.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) hfa
    (fun s hs hguard => (le_abs_self _).trans
      ((hd s (Ico_subset_Icc_self hs)).2 hguard)) htime' b hbI
  have hfb' : f b / Q ≤ 2 * D := by
    apply (div_le_iff₀ hQ).mpr
    simpa only [mul_assoc] using hfb
  have herr := (abs_lt.mp (hk.2.2 b hbI (hk.1 hbI) x (mem_singleton x))).1
  have hetaLe := min_le_right
    ((D - (G.limit.flow.connection a).scalarCurvature x) / 2)
    (((G.limit.flow.connection b).scalarCurvature x - 2 * D) / 2)
  dsimp only [f] at hfb'
  rw [Cylinder.scalarAlong_of_mem e x hbI] at hfb'
  change (S.flow (G.subsequence k)).scalar
    ((G.embedding k).pointMap b (hk.1 hbI) x) / Q ≤ 2 * D at hfb'
  dsimp only [eta] at herr
  dsimp only [Q] at hfb'
  linarith

theorem exists_finite_scalar_bound_of_left_extension
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    {epsilon canonicalConstant kappa r0 mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r0 mu)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (f : ℝ → G.limit.carrier.carrier → ℝ)
    (hcont : ∀ x, ContinuousOn (fun t => f t x) (Icc (-T) 0))
    (heq : ∀ t ∈ Ioc (-T) 0, ∀ x,
      f t x = (G.limit.flow.connection t).scalarCurvature x)
    {B : ℝ} (hleft : ∀ x, f (-T) x ≤ B) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ t ∈ Ioc (-T) 0, ∀ x,
      (G.limit.flow.connection t).scalarCurvature x ≤ B' := by
  let D := max 4 (B + 1)
  have hD : 4 ≤ D := le_max_left _ _
  have hDpos : 0 < D := by linarith
  have hBD : B < D := lt_of_lt_of_le (lt_add_one B) (le_max_right _ _)
  let delta := min (T / 2) (1 / (8 * H.analytic_constant * D))
  have hden : 0 < 8 * H.analytic_constant * D := by
    positivity [H.analytic_constant_pos]
  have hdelta : 0 < delta := lt_min (half_pos hT) (one_div_pos.mpr hden)
  have hdeltaT : delta ≤ T / 2 := min_le_left _ _
  have htime : 8 * H.analytic_constant * D * delta ≤ 1 := by
    have h := (le_div_iff₀ hden).mp
      (min_le_right (T / 2) (1 / (8 * H.analytic_constant * D)))
    simpa only [delta, mul_comm] using h
  have htail : Icc (-T + delta) 0 ⊆ Ioc (-T) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨K, hK, hcurvature⟩ :=
    G.limit.curvature_locally_bounded_in_time (Icc (-T + delta) 0)
      isCompact_Icc htail
  refine ⟨max (2 * D) (9 * K), (by positivity), ?_⟩
  intro t ht x
  by_cases hnear : t ≤ -T + delta
  · obtain ⟨r, hr, hclose⟩ := Metric.continuousWithinAt_iff.mp
      (hcont x (-T) ⟨le_rfl, by linarith⟩) (D - B) (sub_pos.mpr hBD)
    let step := min ((t + T) / 2) (r / 2)
    have hstep : 0 < step := lt_min (half_pos (by linarith [ht.1])) (half_pos hr)
    have hstepTime : step ≤ (t + T) / 2 := min_le_left _ _
    have hstepRadius : step ≤ r / 2 := min_le_right _ _
    let a := -T + step
    have ha : -T < a := by dsimp only [a]; linarith
    have hat : a < t := by dsimp only [a]; linarith [ht.1]
    have haI : a ∈ Ioc (-T) 0 := ⟨ha, hat.le.trans ht.2⟩
    have hdist : dist a (-T) < r := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ha)]
      dsimp only [a]
      linarith
    have hfa : (G.limit.flow.connection a).scalarCurvature x < D := by
      have hc := hclose ⟨ha.le, haI.2⟩ hdist
      rw [Real.dist_eq] at hc
      have hupper := (abs_lt.mp hc).2
      rw [← heq a haI x]
      linarith [hleft x]
    have hIJ : Icc a t ⊆ Ioc (-T) 0 := by
      intro s hs
      exact ⟨ha.trans_le hs.1, hs.2.trans ht.2⟩
    have hlength : t - a ≤ delta := by linarith
    have htime' : 8 * H.analytic_constant * D * (t - a) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlength hden.le).trans htime
    exact (generalized_limit_scalar_le_double hC H G hat.le ht.2 hIJ hD htime'
      x hfa).trans (le_max_left _ _)
  · have htailMem : t ∈ Icc (-T + delta) 0 := ⟨le_of_lt (lt_of_not_ge hnear), ht.2⟩
    have hscalar := (le_abs_self _).trans
      (((G.limit.flow.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
        (mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (hcurvature t htailMem x)) (sq_nonneg (3 : ℝ))))
    norm_num only [Nat.cast_ofNat, sq] at hscalar
    exact hscalar.trans (le_max_right _ _)

end PoincareConjecture.M30
