import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Real









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

private theorem symmetric_gaussian_le_one_sided
    (n : ℕ) {A B c A0 d t Vx Vy : ℝ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hA0 : 0 < A0)
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t ≤ 1) (hx : 0 < Vx) (hy : 0 < Vy)
    (hvol : Vx ≤ A * ((d + Real.sqrt t) / Real.sqrt t) ^ n *
      Real.exp (B * (d + Real.sqrt t)) * Vy) :
    A0 / (Real.sqrt Vx * Real.sqrt Vy) * Real.exp (-d ^ 2 / (c * t)) ≤
      (A0 * A * Real.exp (B + c * ((n : ℝ) + B) ^ 2 / 2)) / Vx *
        Real.exp (-d ^ 2 / ((2 * c) * t)) := by
  let r := Real.sqrt t
  let s := d / r
  let α := (n : ℝ) + B
  let Q := A * Real.exp (B + α * s)
  have hr : 0 < r := Real.sqrt_pos.mpr ht
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hr2 : r ^ 2 = t := Real.sq_sqrt ht.le
  have hs : 0 ≤ s := div_nonneg hd hr.le
  have hα : 0 ≤ α := add_nonneg (Nat.cast_nonneg _) hB
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hA
    (Real.one_le_exp_iff.mpr (add_nonneg hB (mul_nonneg hα hs)))
  have hratio : (d + r) / r = 1 + s := by
    dsimp [s]
    rw [add_div, div_self hr.ne']
    ring
  have hd_le : d ≤ s := by
    calc
      d = s * r := (div_mul_cancel₀ d hr.ne').symm
      _ ≤ s := mul_le_of_le_one_right hs hr1
  have hpow : (1 + s) ^ n ≤ Real.exp ((n : ℝ) * s) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp s) n
  have hfactor : A * ((d + r) / r) ^ n * Real.exp (B * (d + r)) ≤ Q := by
    rw [hratio]
    calc
      A * (1 + s) ^ n * Real.exp (B * (d + r)) ≤
          A * Real.exp ((n : ℝ) * s) * Real.exp (B * (s + 1)) := by
        gcongr
      _ = Q := by
        dsimp [Q, α]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hv : Vx ≤ Q * Vy := hvol.trans (mul_le_mul_of_nonneg_right hfactor hy.le)
  have hsqrt : Real.sqrt Vx ≤ Q * Real.sqrt Vy := by
    apply (Real.sqrt_le_left (mul_nonneg (zero_le_one.trans hQ) (Real.sqrt_nonneg _))).mpr
    rw [mul_pow, Real.sq_sqrt hy.le]
    exact hv.trans (mul_le_mul_of_nonneg_right (by nlinarith : Q ≤ Q ^ 2) hy.le)
  have hden : A0 / (Real.sqrt Vx * Real.sqrt Vy) ≤ A0 * Q / Vx := by
    apply (div_le_div_iff₀
      (mul_pos (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hy)) hx).mpr
    have h := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg Vx)
    have hsq : Real.sqrt Vx * Real.sqrt Vx = Vx := by
      simpa only [pow_two] using Real.sq_sqrt hx.le
    rw [hsq] at h
    nlinarith
  have hscale : d ^ 2 / (c * t) = s ^ 2 / c := by
    dsimp [s]
    rw [div_pow, hr2]
    field_simp
  have hscale2 : d ^ 2 / ((2 * c) * t) = s ^ 2 / (2 * c) := by
    dsimp [s]
    rw [div_pow, hr2]
    field_simp
  have hcomplete : α * s - s ^ 2 / c ≤ c * α ^ 2 / 2 - s ^ 2 / (2 * c) := by
    have hsq : α * s - c * α ^ 2 / 2 ≤ s ^ 2 / (2 * c) :=
      (le_div_iff₀ (mul_pos (by norm_num) hc)).mpr (by
        nlinarith [sq_nonneg (s - c * α)])
    have heq : s ^ 2 / c = 2 * (s ^ 2 / (2 * c)) := by ring
    linarith
  calc
    A0 / (Real.sqrt Vx * Real.sqrt Vy) * Real.exp (-d ^ 2 / (c * t)) ≤
        A0 * Q / Vx * Real.exp (-d ^ 2 / (c * t)) :=
      mul_le_mul_of_nonneg_right hden (Real.exp_pos _).le
    _ = (A0 * A / Vx) * Real.exp (B + α * s - s ^ 2 / c) := by
      rw [neg_div, hscale]
      dsimp [Q]
      rw [show A0 * (A * Real.exp (B + α * s)) / Vx =
        (A0 * A / Vx) * Real.exp (B + α * s) by ring, mul_assoc, ← Real.exp_add]
      rfl
    _ ≤ (A0 * A / Vx) * Real.exp (B + c * α ^ 2 / 2 - s ^ 2 / (2 * c)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (div_nonneg (mul_nonneg hA0.le (zero_le_one.trans hA)) hx.le)
      linarith only [hcomplete]
    _ = (A0 * A * Real.exp (B + c * ((n : ℝ) + B) ^ 2 / 2)) / Vx *
        Real.exp (-d ^ 2 / ((2 * c) * t)) := by
      rw [neg_div, hscale2, Real.exp_sub]
      dsimp [α]
      rw [Real.exp_neg]
      ring




theorem exists_gaussian_normalization_constant
    (n : ℕ) (A B c A0 : ℝ)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hA0 : 0 < A0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [PreconnectedSpace M] (g : RiemannianMetric n M),
        (∀ x : M, ∀ r > 0, 0 < g.volumeMeasure (g.ball x r) ∧
          g.volumeMeasure (g.ball x r) < ⊤) →
        (∀ x : M, ∀ r R : ℝ, 0 < r → r ≤ R →
          g.volumeMeasure.real (g.ball x R) ≤ A * (R / r) ^ n * Real.exp (B * R) *
            g.volumeMeasure.real (g.ball x r)) →
        ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ (x y : M) (h : ℝ),
          h ≤ A0 / (Real.sqrt (g.volumeMeasure.real (g.ball x (Real.sqrt t))) *
            Real.sqrt (g.volumeMeasure.real (g.ball y (Real.sqrt t)))) *
              Real.exp (-(g.edist x y).toReal ^ 2 / (c * t)) →
          h ≤ C / g.volumeMeasure.real (g.ball x (Real.sqrt t)) *
            Real.exp (-(g.edist x y).toReal ^ 2 / ((2 * c) * t)) := by
  refine ⟨A0 * A * Real.exp (B + c * ((n : ℝ) + B) ^ 2 / 2),
    mul_pos (mul_pos hA0 (zero_lt_one.trans_le hA)) (Real.exp_pos _), ?_⟩
  intro M _ _ _ _ _ _ _ g hballs hgrowth t ht ht1 x y h hgauss
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace (fun x y => g.edist_ne_top x y)
  have hdist (p q : M) : dist p q = (g.edist p q).toReal := rfl
  have hball (p : M) (r : ℝ) : Metric.ball p r = g.ball p r := by
    ext q
    change dist q p < r ↔ EDist.edist p q < ENNReal.ofReal r
    rw [dist_comm, edist_lt_ofReal]
  let r := Real.sqrt t
  have hr : 0 < r := Real.sqrt_pos.mpr ht
  have hR : 0 < dist x y + r := add_pos_of_nonneg_of_pos dist_nonneg hr
  have hsub : g.ball x r ⊆ g.ball y (dist x y + r) := by
    rw [← hball, ← hball]
    intro z hz
    have hz' : dist z x < r := hz
    exact (dist_triangle z x y).trans_lt (by linarith)
  have hvol : g.volumeMeasure.real (g.ball x r) ≤
      A * ((dist x y + r) / r) ^ n * Real.exp (B * (dist x y + r)) *
        g.volumeMeasure.real (g.ball y r) :=
    (measureReal_mono hsub (hballs y _ hR).2.ne).trans
      (hgrowth y r (dist x y + r) hr (by have := dist_nonneg (x := x) (y := y); linarith))
  apply hgauss.trans
  apply symmetric_gaussian_le_one_sided n hA hB hc hA0 ENNReal.toReal_nonneg ht ht1
    (ENNReal.toReal_pos (hballs x r hr).1.ne' (hballs x r hr).2.ne)
    (ENNReal.toReal_pos (hballs y r hr).1.ne' (hballs y r hr).2.ne)
  simpa only [hdist, r, Measure.real] using hvol

end PoincareConjecture.RiemannianMetric
