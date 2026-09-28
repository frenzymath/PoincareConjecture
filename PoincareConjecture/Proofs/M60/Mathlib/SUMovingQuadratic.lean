import PoincareConjecture.Proofs.M60.Mathlib.SURegularizedQuadratic

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem suRegularizedQuadratic_metric_comparison
    (B A : E →L[ℝ] E →L[ℝ] ℝ) {a d c p : ℝ}
    (ha : 0 < a) (hd : ‖B - A‖ ≤ d) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hB : ∀ v, 0 ≤ B v v) (hA : ∀ v, a * ‖v‖ ^ 2 ≤ A v v) (v : E) :
    suRegularizedQuadratic B c p v ≤
      (1 + d / a) ^ p * suRegularizedQuadratic A c p v := by
  have hd0 : 0 ≤ d := (norm_nonneg (B - A)).trans hd
  have hA0 : 0 ≤ A v v := (mul_nonneg ha.le (sq_nonneg _)).trans (hA v)
  have hdiff : B v v - A v v ≤ d * ‖v‖ ^ 2 := by
    calc
      B v v - A v v ≤ ‖(B - A) v v‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using le_abs_self (B v v - A v v)
      _ ≤ ‖B - A‖ * ‖v‖ * ‖v‖ := (B - A).le_opNorm₂ v v
      _ ≤ d * ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hsmall : d * ‖v‖ ^ 2 ≤ (d / a) * A v v := by
    have := mul_le_mul_of_nonneg_left (hA v) (div_nonneg hd0 ha.le)
    have hcancel : d / a * a = d := div_mul_cancel₀ d ha.ne'
    nlinarith
  have hbase : c + B v v ≤ (1 + d / a) * (c + A v v) := by
    nlinarith [mul_nonneg (div_nonneg hd0 ha.le) hc]
  calc
    suRegularizedQuadratic B c p v ≤ ((1 + d / a) * (c + A v v)) ^ p :=
      Real.rpow_le_rpow (add_nonneg hc (hB v)) hbase hp
    _ = _ := Real.mul_rpow (by positivity) (add_nonneg hc hA0)

section Measurable

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

local instance : MeasurableSpace (E →L[ℝ] E →L[ℝ] ℝ) := borel _
local instance : BorelSpace (E →L[ℝ] E →L[ℝ] ℝ) := ⟨rfl⟩

theorem suMovingRegularizedQuadratic_le_liminf
    (B : X → E →L[ℝ] E →L[ℝ] ℝ)
    (A : ℕ → X → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Measurable B) (hA : ∀ n, Measurable (A n))
    (hpos : ∀ x v, 0 ≤ B x v v)
    {a : ℝ} (ha : 0 < a) (hcoerc : ∀ n x v, a * ‖v‖ ^ 2 ≤ A n x v v)
    {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hd0 : ∀ n, 0 ≤ d n) (hclose : ∀ n x, ‖B x - A n x‖ ≤ d n)
    (c : X → ℝ) (hc : Measurable c) (hc0 : ∀ x, 0 ≤ c x)
    {p : ℝ} (hp : 1 ≤ p)
    {u : ℕ → Lp E 2 mu} {v : Lp E 2 mu}
    (hw : ∀ L : StrongDual ℝ (Lp E 2 mu),
      Tendsto (fun n => L (u n)) atTop (𝓝 (L v))) :
    (∫⁻ x, ENNReal.ofReal (suRegularizedQuadratic (B x) (c x) p (v x)) ∂mu) ≤
      liminf (fun n => ∫⁻ x,
        ENNReal.ofReal (suRegularizedQuadratic (A n x) (c x) p (u n x)) ∂mu) atTop := by
  let t : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((1 + d n / a) ^ p)
  let I : ℕ → ℝ≥0∞ := fun n => ∫⁻ x,
    ENNReal.ofReal (suRegularizedQuadratic (A n x) (c x) p (u n x)) ∂mu
  have ht : Tendsto t atTop (𝓝 1) := by
    have hbase : Tendsto (fun n => 1 + d n / a) atTop (𝓝 (1 : ℝ)) := by
      simpa using (hd.div_const a).const_add 1
    simpa [t, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hbase.rpow_const (Or.inr (show 0 ≤ p by linarith)))
  have hcomp (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (suRegularizedQuadratic (B x) (c x) p (u n x)) ∂mu) ≤
        t n * I n := by
    calc
      _ ≤ ∫⁻ x, t n *
          ENNReal.ofReal (suRegularizedQuadratic (A n x) (c x) p (u n x)) ∂mu := by
        apply lintegral_mono
        intro x
        dsimp only [t]
        rw [← ENNReal.ofReal_mul
          (Real.rpow_nonneg (add_nonneg zero_le_one (div_nonneg (hd0 n) ha.le)) p)]
        exact ENNReal.ofReal_le_ofReal (suRegularizedQuadratic_metric_comparison
          (B x) (A n x) ha (hclose n x) (hc0 x) (by linarith) (hpos x) (hcoerc n x) _)
      _ = _ := lintegral_const_mul'' _
        (suConvexIntegral_aemeasurable _
          (suRegularizedQuadratic_measurable (A n) (hA n) c hc (by linarith)) (u n))
  have hmul : liminf (fun n => t n * I n) atTop ≤ liminf I atTop := by
    have h := ENNReal.liminf_mul_le (u := t) (v := I) (f := atTop)
      (Or.inl (by rw [ht.limsup_eq]; exact one_ne_zero))
      (Or.inl (by rw [ht.limsup_eq]; exact ENNReal.one_ne_top))
    change liminf (fun n => t n * I n) atTop ≤ limsup t atTop * liminf I atTop at h
    simpa only [ht.limsup_eq, one_mul] using h
  exact (suRegularizedQuadratic_le_liminf B hB hpos c hc hc0 hp hw).trans
    ((liminf_le_liminf (Eventually.of_forall hcomp)).trans hmul)

end Measurable

end PoincareConjecture.M60
