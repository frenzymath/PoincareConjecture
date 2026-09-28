import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteDistanceSlab
import Mathlib.Analysis.SpecificLimits.Basic









set_option autoImplicit false

open Set Filter Finset
open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareConjecture.M47

private theorem dyadic_increment_eq {Q T : ℝ} (hQ : 0 < Q) (m : ℕ) :
    (12 * (Real.sqrt Q * (3 / 2) ^ m) +
      8 * (Q * 2 ^ m) / (Real.sqrt Q * (3 / 2) ^ m)) * (T * (1 / 2) ^ m) =
        12 * T * Real.sqrt Q * (3 / 4) ^ m +
          8 * T * Real.sqrt Q * (2 / 3) ^ m := by
  have hroot : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hp : (3 / 2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdiv : Q * 2 ^ m / (Real.sqrt Q * (3 / 2) ^ m) =
      Real.sqrt Q * (4 / 3) ^ m := by
    calc
      _ = (Real.sqrt Q * Real.sqrt Q) * 2 ^ m /
          (Real.sqrt Q * (3 / 2) ^ m) := by rw [Real.mul_self_sqrt hQ.le]
      _ = Real.sqrt Q * (2 ^ m / (3 / 2) ^ m) := by field_simp
      _ = Real.sqrt Q * (4 / 3) ^ m := by rw [← div_pow]; norm_num
  rw [show 8 * (Q * 2 ^ m) / (Real.sqrt Q * (3 / 2) ^ m) =
    8 * (Q * 2 ^ m / (Real.sqrt Q * (3 / 2) ^ m)) by ring, hdiv]
  calc
    _ = 12 * T * Real.sqrt Q * ((3 / 2) ^ m * (1 / 2) ^ m) +
        8 * T * Real.sqrt Q * ((4 / 3) ^ m * (1 / 2) ^ m) := by ring
    _ = _ := by rw [← mul_pow, ← mul_pow]; norm_num

private theorem dyadic_increment_le {Q T : ℝ} (hQ : 0 < Q) (hT : 0 < T) (j : ℕ) :
    (12 * (Real.sqrt Q * (3 / 2) ^ (j + 1)) +
      8 * (Q * 2 ^ (j + 1)) / (Real.sqrt Q * (3 / 2) ^ (j + 1))) *
        (T * (1 / 2) ^ (j + 1)) ≤ 20 * T * Real.sqrt Q * (3 / 4) ^ j := by
  rw [dyadic_increment_eq hQ]
  have hp : (2 / 3 : ℝ) ^ (j + 1) ≤ (3 / 4 : ℝ) ^ (j + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hlast : (3 / 4 : ℝ) ^ (j + 1) ≤ (3 / 4 : ℝ) ^ j := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) j]
  calc
    _ ≤ 12 * T * Real.sqrt Q * (3 / 4) ^ (j + 1) +
        8 * T * Real.sqrt Q * (3 / 4) ^ (j + 1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = 20 * T * Real.sqrt Q * (3 / 4) ^ (j + 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlast (by positivity)

private theorem finite_dyadic_budget {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (f : ℝ → ℝ) (hmono : AntitoneOn f (Ioc (-T) 0))
    (hslab : ∀ a b scale : ℝ, -T < a → a ≤ b → b ≤ 0 → 0 < scale →
      f a ≤ f b + (12 * scale + 8 * (Q * T / (a + T)) / scale) * (b - a))
    {t : ℝ} (ht : t ∈ Ioc (-T) 0) : f t ≤ f 0 + 80 * T * Real.sqrt Q := by
  let a : ℕ → ℝ := fun j => -T + T * (1 / 2) ^ j
  have ha (j : ℕ) : a j ∈ Ioc (-T) 0 := by
    dsimp only [a]
    constructor
    · have := mul_pos hT (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j)
      linarith
    · have := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (n := j)) hT.le
      linarith
  have hstep (j : ℕ) : f (a (j + 1)) ≤ f (a j) +
      20 * T * Real.sqrt Q * (3 / 4) ^ j := by
    have hgap : a j - a (j + 1) = T * (1 / 2) ^ (j + 1) := by
      dsimp only [a]
      rw [pow_succ]
      ring
    have htime : a (j + 1) ≤ a j := by
      have : 0 ≤ T * (1 / 2) ^ (j + 1) := by positivity
      linarith
    have hcoef : Q * T / (a (j + 1) + T) = Q * 2 ^ (j + 1) := by
      have hp : (1 / 2 : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hden : a (j + 1) + T = T * (1 / 2) ^ (j + 1) := by dsimp [a]; ring
      rw [hden]
      apply (div_eq_iff (mul_ne_zero hT.ne' hp)).mpr
      have hcancel : (2 : ℝ) ^ (j + 1) * (1 / 2) ^ (j + 1) = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        Q * T = Q * T * (2 ^ (j + 1) * (1 / 2) ^ (j + 1)) := by rw [hcancel, mul_one]
        _ = _ := by ring
    have h := hslab (a (j + 1)) (a j) (Real.sqrt Q * (3 / 2) ^ (j + 1))
      (ha _).1 htime (ha _).2 (by positivity)
    rw [hcoef, hgap] at h
    exact h.trans (add_le_add le_rfl (dyadic_increment_le hQ hT j))
  have hchain (N : ℕ) : f (a N) ≤ f 0 +
      20 * T * Real.sqrt Q * ∑ j ∈ range N, (3 / 4 : ℝ) ^ j := by
    induction N with
    | zero => simp [a]
    | succ N ih =>
      have h := (hstep N).trans (add_le_add ih le_rfl)
      simpa only [sum_range_succ, mul_add, add_assoc] using h
  have hsum (N : ℕ) : (∑ j ∈ range N, (3 / 4 : ℝ) ^ j) ≤ 4 := by
    have h := geom_sum_mul_neg (3 / 4 : ℝ) N
    have hp := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) N
    nlinarith
  have hlim : Tendsto a atTop (𝓝 (-T)) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hp.const_mul T)
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds ht.1)).exists
  calc
    f t ≤ f (a N) := hmono (ha N) ht hN.le
    _ ≤ f 0 + 20 * T * Real.sqrt Q * ∑ j ∈ range N, (3 / 4 : ℝ) ^ j := hchain N
    _ ≤ f 0 + 20 * T * Real.sqrt Q * 4 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hsum N) (by positivity))
    _ = _ := by ring

private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold


theorem limitFinite_distance_budget (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ} (hQ : 0 < Q)
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (x y : L.carrier.carrier) :
    ((L.flow.metric 0).edist x y).toReal ≤ ((L.flow.metric t).edist x y).toReal ∧
      ((L.flow.metric t).edist x y).toReal ≤ ((L.flow.metric 0).edist x y).toReal +
        80 * H.toReal * Real.sqrt Q := by
  refine ⟨limitFinite_distance_antitone h04 hH hfinite L hQ hQ0 ht L.zero_mem ht.1 x y, ?_⟩
  apply finite_dyadic_budget (limitFinite_horizon_pos hH hfinite) hQ
    (fun τ => ((L.flow.metric τ).edist x y).toReal) ?_ ?_
    (by rwa [← limitFinite_domain_eq hfinite])
  · intro a ha b hb hab
    exact limitFinite_distance_antitone h04 hH hfinite L hQ hQ0
      (by rwa [limitFinite_domain_eq hfinite])
      (by rwa [limitFinite_domain_eq hfinite]) hab x y
  · intro a b scale ha hab hb hscale
    exact limitFinite_distance_slab h04 hH hfinite L hQ hQ0 ha hab hb hscale x y


theorem limitFinite_additive_distance (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {B0 : ℝ}
    (hterminal : ∀ x : L.carrier.carrier,
      (L.flow.connection 0).curvatureTensorNorm x ≤ B0)
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (x y : L.carrier.carrier) :
    ((L.flow.metric 0).edist x y).toReal ≤ ((L.flow.metric t).edist x y).toReal ∧
      ((L.flow.metric t).edist x y).toReal ≤ ((L.flow.metric 0).edist x y).toReal +
        80 * H.toReal * Real.sqrt (max 1 (3 * B0)) := by
  apply limitFinite_distance_budget h04 hH hfinite L
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) ?_ t ht x y
  intro z
  exact ((L.flow.connection 0).scalarCurvature_le_curvatureTensorNorm_sharp z).trans
    ((mul_le_mul_of_nonneg_left (hterminal z) (by norm_num)).trans (le_max_right _ _))

end PoincareConjecture.M47
