import PoincareConjecture.Proofs.M47.TerminalCommonIntervalGlobalLimits
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalDistanceLimit
import Mathlib.Topology.MetricSpace.Isometry









set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal NNReal

universe u

namespace PoincareConjecture.M47



theorem terminalCommonInterval_isometry_of_ball_control
    {M N : Type u} [MetricSpace M] [MetricSpace N]
    [ProperSpace M] [ProperSpace N] (p : M) (q : N)
    (T : ℕ → OpenPartialHomeomorph M N)
    (hcontrol : ∀ R : ℝ, 0 < R → ∀ lambda : ℝ, 0 < lambda → lambda < 1 →
      ∀ᶠ n in atTop,
        Metric.closedBall p R ⊆ (T n).source ∧
        MapsTo (T n) (Metric.closedBall p R) (Metric.ball q (4 * (R + 1))) ∧
        Metric.closedBall q R ⊆ (T n).target ∧
        MapsTo (T n).symm (Metric.closedBall q R) (Metric.ball p (4 * (R + 1))) ∧
        (∀ x ∈ Metric.closedBall p R, ∀ y ∈ Metric.closedBall p R,
          ENNReal.ofReal (lambda ^ 2) * edist x y ≤ edist (T n x) (T n y) ∧
          edist (T n x) (T n y) ≤ ENNReal.ofReal (lambda⁻¹ ^ 2) * edist x y) ∧
        (∀ x ∈ Metric.closedBall q R, ∀ y ∈ Metric.closedBall q R,
          ENNReal.ofReal (lambda ^ 2) * edist x y ≤ edist ((T n).symm x) ((T n).symm y) ∧
          edist ((T n).symm x) ((T n).symm y) ≤
            ENNReal.ofReal (lambda⁻¹ ^ 2) * edist x y) ∧
        T n p = q ∧ (T n).symm q = p) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ d : M ≃ᵢ N, d p = q ∧
      (∀ j : ℕ, TendstoUniformlyOn (fun n => T (rho n)) d atTop
        (Metric.closedBall p (j + 1))) ∧
      (∀ j : ℕ, TendstoUniformlyOn (fun n => (T (rho n)).symm) d.symm atTop
        (Metric.closedBall q (j + 1))) := by
  let K (j : ℕ) := Metric.closedBall p (j + 1)
  let L (j : ℕ) := Metric.closedBall q (j + 1)
  let K' (j : ℕ) := Metric.closedBall p (4 * (j + 2))
  let L' (j : ℕ) := Metric.closedBall q (4 * (j + 2))
  have (j : ℕ) : CompactSpace (K j) := inferInstance
  have (j : ℕ) : CompactSpace (L j) := inferInstance
  have (j : ℕ) : CompactSpace (K' j) := inferInstance
  have (j : ℕ) : CompactSpace (L' j) := inferInstance
  have hcover {X : Type u} [MetricSpace X] (a x : X) :
      ∃ j : ℕ, x ∈ interior (Metric.closedBall a (j + 1)) := by
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x a)
    refine ⟨j, Metric.ball_subset_interior_closedBall ?_⟩
    change dist x a < (j : ℝ) + 1
    linarith
  have hKcover : ∀ x, ∃ j, x ∈ interior (K j) := hcover p
  have hLcover : ∀ y, ∃ j, y ∈ interior (L j) := hcover q
  have hT (j : ℕ) : ∀ᶠ n in atTop, MapsTo (T n) (K j) (L' j) ∧
      LipschitzOnWith 4 (T n) (K j) := by
    filter_upwards [hcontrol (j + 1) (by positivity) (1 / 2) (by norm_num)
      (by norm_num)] with n hn
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · have hm := Metric.ball_subset_closedBall (hn.2.1 hx)
      change dist (T n x) q ≤ 4 * ((j : ℝ) + 2)
      exact (Metric.mem_closedBall.mp hm).trans_eq (by ring)
    · have hb := (hn.2.2.2.2.1 x hx y hy).2
      norm_num at hb ⊢
      exact hb
  have hS (j : ℕ) : ∀ᶠ n in atTop, MapsTo (T n).symm (L j) (K' j) ∧
      LipschitzOnWith 4 (T n).symm (L j) := by
    filter_upwards [hcontrol (j + 1) (by positivity) (1 / 2) (by norm_num)
      (by norm_num)] with n hn
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · have hm := Metric.ball_subset_closedBall (hn.2.2.2.1 hx)
      change dist ((T n).symm x) p ≤ 4 * ((j : ℝ) + 2)
      exact (Metric.mem_closedBall.mp hm).trans_eq (by ring)
    · have hb := (hn.2.2.2.2.2.1 x hx y hy).2
      norm_num at hb ⊢
      exact hb
  obtain ⟨rho, hrho, f, g, hf, hg, hforward, hreverse⟩ :=
    terminalCommonInterval_global_paired_limits K K' L L' hKcover hLcover p q
      (fun j => Metric.mem_closedBall_self (by positivity))
      (fun j => Metric.mem_closedBall_self (by positivity)) 4
      (fun n => T n) (fun n => (T n).symm) hT hS
  have hsource (x : M) : ∀ᶠ n in atTop, x ∈ (T (rho n)).source := by
    obtain ⟨j, hj⟩ := hKcover x
    filter_upwards [hrho.tendsto_atTop.eventually
      (hcontrol (j + 1) (by positivity) (1 / 2) (by norm_num) (by norm_num))] with n hn
    exact hn.1 (interior_subset hj)
  have htarget (y : N) : ∀ᶠ n in atTop, y ∈ (T (rho n)).target := by
    obtain ⟨j, hj⟩ := hLcover y
    filter_upwards [hrho.tendsto_atTop.eventually
      (hcontrol (j + 1) (by positivity) (1 / 2) (by norm_num) (by norm_num))] with n hn
    exact hn.2.2.1 (interior_subset hj)
  have hbase : ∀ᶠ n in atTop, T (rho n) p = q ∧ (T (rho n)).symm q = p := by
    filter_upwards [hrho.tendsto_atTop.eventually
      (hcontrol 1 (by norm_num) (1 / 2) (by norm_num) (by norm_num))] with n hn
    exact hn.2.2.2.2.2.2
  obtain ⟨hleft, hright, hfp, _hgq⟩ := terminalCommonInterval_global_inverse_limits
    K L hKcover hLcover (fun n => T (rho n)) f g hf hg hforward hreverse
      hsource htarget p q hbase
  have hpoint (x : M) : Tendsto (fun n => T (rho n) x) atTop (𝓝 (f x)) := by
    obtain ⟨j, hj⟩ := hKcover x
    exact (hforward j).tendsto_at (interior_subset hj)
  have hisometry : Isometry f := by
    intro x y
    let R := dist x p + dist y p + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hx : x ∈ Metric.closedBall p R := by
      change dist x p ≤ R
      dsimp [R]
      linarith only [dist_nonneg (x := y) (y := p)]
    have hy : y ∈ Metric.closedBall p R := by
      change dist y p ≤ R
      dsimp [R]
      linarith only [dist_nonneg (x := x) (y := p)]
    have he := (hpoint x).edist (hpoint y)
    have hb (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
        ENNReal.ofReal r * edist x y ≤ edist (f x) (f y) ∧
          edist (f x) (f y) ≤ ENNReal.ofReal r⁻¹ * edist x y := by
      have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have hsqrt1 : Real.sqrt r < 1 := by
        simpa using (Real.sqrt_lt_sqrt hr.le hr1)
      have ht := hrho.tendsto_atTop.eventually
        (hcontrol R hR (Real.sqrt r) hsqrt hsqrt1)
      have hlow : ∀ᶠ n in atTop,
          ENNReal.ofReal r * edist x y ≤ edist (T (rho n) x) (T (rho n) y) := by
        filter_upwards [ht] with n hn
        simpa only [Real.sq_sqrt hr.le] using (hn.2.2.2.2.1 x hx y hy).1
      have hupp : ∀ᶠ n in atTop,
          edist (T (rho n) x) (T (rho n) y) ≤ ENNReal.ofReal r⁻¹ * edist x y := by
        filter_upwards [ht] with n hn
        simpa only [inv_pow, Real.sq_sqrt hr.le] using (hn.2.2.2.2.1 x hx y hy).2
      exact ⟨ge_of_tendsto he hlow, le_of_tendsto he hupp⟩
    exact terminalCommonInterval_distance_eq_of_all_factors
      (fun r hr hr1 => (hb r hr hr1).1) (fun r hr hr1 => (hb r hr hr1).2)
  let d : M ≃ᵢ N :=
    { toEquiv := ⟨f, g, hleft, hright⟩
      isometry_toFun := hisometry }
  exact ⟨rho, hrho, d, hfp, hforward, hreverse⟩

end PoincareConjecture.M47
