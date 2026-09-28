import PoincareConjecture.Proofs.M35.CapGeometry.InitialIntrinsicProfile










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35.Uniqueness



theorem initial_intrinsic_radius_jets_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (t s : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta) (hs : ∀ k, 0 < s k)
    {t₀ : ℝ} (ht₀ : t₀ < 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (hslim : Tendsto s atTop atTop) (m : ℕ) :
    Tendsto (fun k => iteratedDeriv m
      (rawWarpingRadius P E.flow.base E.rotation_invariant (t k)) (s k))
      atTop (𝓝 (if m = 0 then Real.sqrt (2 * (1 - t₀)) else 0)) := by
  cases m with
  | zero =>
    have h := (Real.continuous_sqrt.tendsto (2 * (1 - t₀))).comp
      (initial_intrinsic_squared_radius_tendsto P E htheta hthetalt t s ht hs
        ht₀ htlim hslim)
    have hpos (k : ℕ) : 0 ≤ rawWarpingRadius P E.flow.base E.rotation_invariant
        (t k) (s k) := by
      have htime : t k ∈ Ico 0 E.flow.base.lifetime :=
        ⟨(ht k).1, (ht k).2.trans_lt hthetalt⟩
      rw [rawWarpingRadius_eq P E.flow.base E.rotation_invariant htime]
      exact (intrinsicWarpingRadius_pos (E.flow.base.flow.metric (t k))
        (E.rotation_invariant (t k) htime) (E.flow.base.complete P htime) (hs k)).le
    simpa only [iteratedDeriv_zero, ite_true, Function.comp_def, Real.sqrt_sq (hpos _)] using h
  | succ m =>
    simpa only [Nat.add_one_ne_zero, ite_false] using
      initial_intrinsic_positive_jets_tendsto_zero P E htheta hthetalt t s ht hslim m



theorem initial_intrinsic_squared_radius_jets_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (t s : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta) (hs : ∀ k, 0 < s k)
    {t₀ : ℝ} (ht₀ : t₀ < 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (hslim : Tendsto s atTop atTop) (m : ℕ) :
    Tendsto (fun k => iteratedDeriv m
      (fun r => rawWarpingRadius P E.flow.base E.rotation_invariant (t k) r ^ 2) (s k))
      atTop (𝓝 (if m = 0 then 2 * (1 - t₀) else 0)) := by
  let f k := rawWarpingRadius P E.flow.base E.rotation_invariant (t k)
  have hjet := initial_intrinsic_radius_jets_tendsto P E htheta hthetalt t s ht hs
    ht₀ htlim hslim
  by_cases hm : m = 0
  · subst m
    simpa only [iteratedDeriv_zero, ite_true] using
      initial_intrinsic_squared_radius_tendsto P E htheta hthetalt t s ht hs
        ht₀ htlim hslim
  · rw [if_neg hm]
    have hf (k : ℕ) : ContDiffAt ℝ m (f k) (s k) := by
      have htime : t k ∈ Ico 0 E.flow.base.lifetime :=
        ⟨(ht k).1, (ht k).2.trans_lt hthetalt⟩
      change ContDiffAt ℝ m (rawWarpingRadius P E.flow.base E.rotation_invariant (t k)) (s k)
      rw [rawWarpingRadius_eq P E.flow.base E.rotation_invariant htime]
      exact (intrinsicWarpingRadius_contDiff _ _ _).contDiffAt.of_le
        (by exact_mod_cast le_top (a := (m : ℕ∞)))
    have hterm (i : ℕ) (_hi : i ∈ Finset.range (m + 1)) :
        Tendsto (fun k => (m.choose i : ℝ) * iteratedDeriv i (f k) (s k) *
          iteratedDeriv (m - i) (f k) (s k)) atTop (𝓝 0) := by
      have h := ((hjet i).const_mul (m.choose i : ℝ)).mul (hjet (m - i))
      have hzero : (m.choose i : ℝ) *
          (if i = 0 then Real.sqrt (2 * (1 - t₀)) else 0) *
          (if m - i = 0 then Real.sqrt (2 * (1 - t₀)) else 0) = 0 := by
        by_cases hi0 : i = 0
        · simp only [hi0, ite_true, Nat.sub_zero, if_neg hm, mul_zero]
        · simp only [if_neg hi0, mul_zero, zero_mul]
      simpa only [hzero, f] using h
    have hsum := tendsto_finsetSum (Finset.range (m + 1)) hterm
    simp only [Finset.sum_const_zero] at hsum
    apply hsum.congr'
    apply Eventually.of_forall
    intro k
    change _ = iteratedDeriv m (fun r => f k r ^ 2) (s k)
    simpa only [pow_two] using (iteratedDeriv_fun_mul (hf k) (hf k)).symm



theorem initial_intrinsic_squared_radius_jets_tendsto_of_escape
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (t s : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta)
    {t₀ : ℝ} (ht₀ : t₀ < 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (hslim : Tendsto s atTop atTop) (m : ℕ) :
    Tendsto (fun k => iteratedDeriv m
      (fun r => rawWarpingRadius P E.flow.base E.rotation_invariant (t k) r ^ 2) (s k))
      atTop (𝓝 (if m = 0 then 2 * (1 - t₀) else 0)) := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hslim.eventually_gt_atTop 0)
  apply (tendsto_add_atTop_iff_nat n).mp
  exact initial_intrinsic_squared_radius_jets_tendsto P E htheta hthetalt
    (fun k => t (k + n)) (fun k => s (k + n)) (fun k => ht (k + n))
    (fun k => hn (k + n) (Nat.le_add_left _ _)) ht₀
    (htlim.comp (tendsto_add_atTop_nat n)) (hslim.comp (tendsto_add_atTop_nat n)) m

end PoincareConjecture.M35.Uniqueness
