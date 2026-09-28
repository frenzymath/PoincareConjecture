import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace PoincareConjecture.M60

variable {X E : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]



def suConvexIntegral (F : X → E → ℝ) (u : Lp E 2 mu) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (F x (u x)) ∂mu

omit [NormedSpace ℝ E] in
theorem suConvexIntegral_aemeasurable (F : X → E → ℝ)
    (hF : Measurable (Function.uncurry F)) (u : Lp E 2 mu) :
    AEMeasurable (fun x => ENNReal.ofReal (F x (u x))) mu := by
  exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
    (hF.comp_aemeasurable (aemeasurable_id.prodMk (Lp.aestronglyMeasurable u).aemeasurable))


theorem suConvexIntegral_sublevel_convex (F : X → E → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hc : ∀ x, ConvexOn ℝ univ (F x)) (C : ℝ≥0∞) :
    Convex ℝ {u : Lp E 2 mu | suConvexIntegral F u ≤ C} := by
  intro u hu v hv a b ha hb hab
  have hab' : ENNReal.ofReal a + ENNReal.ofReal b = 1 := by
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  calc
    suConvexIntegral F (a • u + b • v) ≤
        ∫⁻ x, ENNReal.ofReal a * ENNReal.ofReal (F x (u x)) +
          ENNReal.ofReal b * ENNReal.ofReal (F x (v x)) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [Lp.coeFn_add (a • u) (b • v),
        Lp.coeFn_smul a u, Lp.coeFn_smul b v] with x hadd hau hbv
      rw [hadd, Pi.add_apply, hau, hbv, Pi.smul_apply, Pi.smul_apply]
      calc
        ENNReal.ofReal (F x (a • u x + b • v x)) ≤
            ENNReal.ofReal (a * F x (u x) + b * F x (v x)) :=
          ENNReal.ofReal_le_ofReal ((hc x).2 (mem_univ _) (mem_univ _) ha hb hab)
        _ ≤ _ := by
          grw [ENNReal.ofReal_add_le]
          rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
    _ = ENNReal.ofReal a * suConvexIntegral F u +
        ENNReal.ofReal b * suConvexIntegral F v := by
      rw [lintegral_add_left' ((suConvexIntegral_aemeasurable F hF u).const_mul _)]
      rw [lintegral_const_mul'' _ (suConvexIntegral_aemeasurable F hF u),
        lintegral_const_mul'' _ (suConvexIntegral_aemeasurable F hF v)]
      rfl
    _ ≤ ENNReal.ofReal a * C + ENNReal.ofReal b * C :=
      add_le_add (mul_le_mul' le_rfl hu) (mul_le_mul' le_rfl hv)
    _ = C := by rw [← add_mul, hab', one_mul]

omit [NormedSpace ℝ E] in


theorem suConvexIntegral_sublevel_closed (F : X → E → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hc : ∀ x, Continuous (F x)) (C : ℝ≥0∞) :
    IsClosed {u : Lp E 2 mu | suConvexIntegral F u ≤ C} := by
  apply IsSeqClosed.isClosed
  intro u v hu huv
  obtain ⟨k, -, hk⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  have hlim : ∀ᵐ x ∂mu, Tendsto
      (fun n => ENNReal.ofReal (F x (u (k n) x))) atTop
      (𝓝 (ENNReal.ofReal (F x (v x)))) := by
    filter_upwards [hk] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hc x).continuousAt.tendsto.comp hx)
  calc
    suConvexIntegral F v =
        ∫⁻ x, liminf (fun n => ENNReal.ofReal (F x (u (k n) x))) atTop ∂mu := by
      apply lintegral_congr_ae
      exact hlim.mono fun x hx => hx.liminf_eq.symm
    _ ≤ liminf (fun n => suConvexIntegral F (u (k n))) atTop :=
      lintegral_liminf_le' (fun n => suConvexIntegral_aemeasurable F hF (u (k n)))
    _ ≤ C := liminf_le_of_le (by isBoundedDefault) fun r hr => by
      obtain ⟨n, hn⟩ := hr.exists
      exact hn.trans (hu (k n))


theorem suConvexIntegral_le_of_weak (F : X → E → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hcont : ∀ x, Continuous (F x)) (hc : ∀ x, ConvexOn ℝ univ (F x))
    {u : ℕ → Lp E 2 mu} {v : Lp E 2 mu}
    (hw : ∀ L : StrongDual ℝ (Lp E 2 mu),
      Tendsto (fun n => L (u n)) atTop (𝓝 (L v)))
    {C : ℝ≥0∞} (hC : ∀ᶠ n in atTop, suConvexIntegral F (u n) ≤ C) :
    suConvexIntegral F v ≤ C := by
  by_contra hv
  obtain ⟨L, r, hr, hrv⟩ := geometric_hahn_banach_closed_point
    (suConvexIntegral_sublevel_convex F hF hc C)
    (suConvexIntegral_sublevel_closed F hF hcont C) hv
  have hle : ∀ᶠ n in atTop, L (u n) ≤ r := hC.mono fun n hn => (hr (u n) hn).le
  exact hrv.not_ge (le_of_tendsto (hw L) hle)



theorem suConvexIntegral_le_liminf (F : X → E → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hcont : ∀ x, Continuous (F x)) (hc : ∀ x, ConvexOn ℝ univ (F x))
    {u : ℕ → Lp E 2 mu} {v : Lp E 2 mu}
    (hw : ∀ L : StrongDual ℝ (Lp E 2 mu),
      Tendsto (fun n => L (u n)) atTop (𝓝 (L v))) :
    suConvexIntegral F v ≤ liminf (fun n => suConvexIntegral F (u n)) atTop := by
  by_contra! hv
  obtain ⟨C, hC, hCv⟩ := exists_between hv
  obtain ⟨L, r, hr, hrv⟩ := geometric_hahn_banach_closed_point
    (suConvexIntegral_sublevel_convex F hF hc C)
    (suConvexIntegral_sublevel_closed F hF hcont C) (not_le.mpr hCv)
  have hL : ∀ᶠ n in atTop, r < L (u n) := (tendsto_order.mp (hw L)).1 r hrv
  have hE : ∀ᶠ n in atTop, C ≤ suConvexIntegral F (u n) := by
    filter_upwards [hL] with n hn
    by_contra! h
    exact (hr (u n) h.le).not_ge hn.le
  exact hC.not_ge (le_liminf_of_le (by isBoundedDefault) hE)

end PoincareConjecture.M60
