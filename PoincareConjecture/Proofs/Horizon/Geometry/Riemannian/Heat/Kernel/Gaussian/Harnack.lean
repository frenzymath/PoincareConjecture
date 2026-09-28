import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.LeviCivitaData

private theorem integrableOn_integral_of_subprobability
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B : Set X}
    (hA : μ A < ⊤) (hB : μ B < ⊤) {F : X → X → ℝ}
    (hmeas : Measurable (fun p : X × X => F p.1 p.2))
    (hnonneg : ∀ x y, 0 ≤ F x y) (hrow : ∀ x, Integrable (F x) μ)
    (hmass : ∀ x, (∫ y, F x y ∂μ) ≤ 1) :
    IntegrableOn (fun x => ∫ y in B, F x y ∂μ) A μ := by
  let : IsFiniteMeasure (μ.restrict B) := ⟨by simpa using hB⟩
  have hm : AEStronglyMeasurable (fun x => ∫ y in B, F x y ∂μ) (μ.restrict A) :=
    hmeas.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  apply (integrableOn_const hA.ne (C := (1 : ℝ))).mono' hm
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (hnonneg x))]
  exact (setIntegral_le_integral (hrow x) (Eventually.of_forall (hnonneg x))).trans
    (hmass x)

theorem heatKernel_le_double_ball_integral_of_harnack
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (hc : MetricComplete g)
    {H : ℝ → M → M → ℝ} {C : ℝ}
    (hmeas : ∀ s, 0 < s → Measurable (fun p : M × M => H s p.1 p.2))
    (hnonneg : ∀ s, 0 < s → ∀ x y, 0 ≤ H s x y)
    (hsymm : ∀ s, 0 < s → ∀ x y, H s x y = H s y x)
    (hrow : ∀ s, 0 < s → ∀ x, Integrable (H s x) g.volumeMeasure)
    (hmass : ∀ s, 0 < s → ∀ x, (∫ y, H s x y ∂g.volumeMeasure) ≤ 1)
    (hharnack : ∀ a b, 0 < a → a < b → ∀ x z y,
      H a x y ≤ H b z y * Real.exp (2 * (n : ℝ) * Real.log (b / a) +
        C * (b - a) + (g.edist x z).toReal ^ 2 / (2 * (b - a))))
    {t : ℝ} (ht : 0 < t) (x y : M) :
    IntegrableOn (fun z => ∫ w in g.ball y (Real.sqrt t), H (3 * t) z w
      ∂g.volumeMeasure) (g.ball x (Real.sqrt t)) g.volumeMeasure ∧
    H t x y ≤ Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 1) /
      (g.volumeMeasure.real (g.ball x (Real.sqrt t)) *
        g.volumeMeasure.real (g.ball y (Real.sqrt t))) *
      (∫ z in g.ball x (Real.sqrt t), ∫ w in g.ball y (Real.sqrt t),
        H (3 * t) z w ∂g.volumeMeasure ∂g.volumeMeasure) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have ht2 : 0 < 2 * t := by positivity
  have ht3 : 0 < 3 * t := by positivity
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hxfinite := g.volumeMeasure_ball_lt_top hc x (Real.sqrt t)
  have hyfinite := g.volumeMeasure_ball_lt_top hc y (Real.sqrt t)
  have hxvol : 0 < g.volumeMeasure.real (g.ball x (Real.sqrt t)) :=
    ENNReal.toReal_pos (g.volumeMeasure_ball_pos x hr).ne' hxfinite.ne
  have hyvol : 0 < g.volumeMeasure.real (g.ball y (Real.sqrt t)) :=
    ENNReal.toReal_pos (g.volumeMeasure_ball_pos y hr).ne' hyfinite.ne
  have hball (p : M) : MeasurableSet (g.ball p (Real.sqrt t)) :=
    (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  have hi := integrableOn_integral_of_subprobability hxfinite hyfinite
    (hmeas (3 * t) ht3) (hnonneg (3 * t) ht3) (hrow (3 * t) ht3) (hmass (3 * t) ht3)
  refine ⟨hi, ?_⟩
  let E := Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 1)
  have hstep (a b : ℝ) (ha : 0 < a) (hab : a < b) (hgap : b - a = t)
      (p q v : M) (hq : q ∈ g.ball p (Real.sqrt t)) :
      H a p v ≤ H b q v * Real.exp (2 * (n : ℝ) * Real.log (b / a) +
        C * t + 1 / 2) := by
    have hdist : (g.edist p q).toReal < Real.sqrt t :=
      ENNReal.toReal_lt_of_lt_ofReal (show g.edist p q < ENNReal.ofReal (Real.sqrt t) from hq)
    have hsq : (g.edist p q).toReal ^ 2 ≤ t := by
      calc
        (g.edist p q).toReal ^ 2 ≤ (Real.sqrt t) ^ 2 := by
          gcongr
        _ = t := Real.sq_sqrt ht.le
    have hd : (g.edist p q).toReal ^ 2 / (2 * t) ≤ 1 / 2 :=
      (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr (by nlinarith)
    have h := hharnack a b ha hab p q v
    rw [hgap] at h
    apply h.trans (mul_le_mul_of_nonneg_left ?_ (hnonneg b (ha.trans hab) q v))
    exact Real.exp_le_exp.mpr (add_le_add_right hd _)
  have hpoint (z : M) (hz : z ∈ g.ball x (Real.sqrt t))
      (w : M) (hw : w ∈ g.ball y (Real.sqrt t)) : H t x y ≤ H (3 * t) z w * E := by
    have h1 := hstep t (2 * t) ht (by linarith) (by ring) x z y hz
    have h2 := hstep (2 * t) (3 * t) ht2 (by linarith) (by ring) y w z hw
    rw [hsymm (2 * t) ht2 y z, hsymm (3 * t) ht3 w z] at h2
    have hr1 : 2 * t / t = 2 := by field_simp
    have hr2 : 3 * t / (2 * t) = 3 / 2 := by field_simp
    rw [hr1] at h1
    rw [hr2] at h2
    have hlogs : Real.log 2 + Real.log (3 / 2) = Real.log 3 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have he : Real.exp (2 * (n : ℝ) * Real.log (3 / 2) + C * t + 1 / 2) *
        Real.exp (2 * (n : ℝ) * Real.log 2 + C * t + 1 / 2) = E := by
      rw [← Real.exp_add]
      congr 1
      nlinarith [hlogs]
    calc
      H t x y ≤ (H (3 * t) z w *
          Real.exp (2 * (n : ℝ) * Real.log (3 / 2) + C * t + 1 / 2)) *
          Real.exp (2 * (n : ℝ) * Real.log 2 + C * t + 1 / 2) :=
        h1.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)
      _ = H (3 * t) z w * E := by rw [mul_assoc, he]
  have havgy (z : M) (hz : z ∈ g.ball x (Real.sqrt t)) :=
    setIntegral_mono_on (integrableOn_const hyfinite.ne)
      ((hrow (3 * t) ht3 z).mul_const E).integrableOn (hball y) (hpoint z hz)
  simp only [setIntegral_const, integral_mul_const, smul_eq_mul] at havgy
  have havgx := setIntegral_mono_on (integrableOn_const hxfinite.ne)
    (hi.mul_const E) (hball x) havgy
  rw [setIntegral_const, integral_mul_const, smul_eq_mul] at havgx
  change H t x y ≤ E / _ * _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hxvol hyvol)).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using havgx

end PoincareConjecture.LeviCivitaData
