import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.Coordinates.FinSucc

set_option autoImplicit false

open MeasureTheory Poincare.EuclideanSpace

namespace Poincare.Coarea

def euclideanConsEquiv (n : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin n)) ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
  (((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm).trans
      (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))

@[simp]
lemma euclideanConsEquiv_apply {n : ℕ} (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    euclideanConsEquiv n p = euclideanCons p.1 p.2 := by
  simp [euclideanConsEquiv, euclideanCons, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]
  exact ⟨rfl, rfl⟩

theorem volumePreserving_euclideanConsEquiv (n : ℕ) :
    MeasurePreserving (euclideanConsEquiv n) := by
  exact (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.comp
      ((MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_ofLp (Fin n))))

lemma measurable_euclideanCons {n : ℕ} (t : ℝ) :
    Measurable (euclideanCons (n := n) t) := by
  simpa [Function.comp_def] using
    (euclideanConsEquiv n).measurable.comp (measurable_const.prodMk measurable_id)

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in

theorem integrable_euclideanCons_iff {F : EuclideanSpace ℝ (Fin (n + 1)) → E} :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin n) => F (euclideanCons p.1 p.2)) ↔
      Integrable F := by
  simpa [Function.comp_def] using
    (volumePreserving_euclideanConsEquiv n).integrable_comp_emb
      (euclideanConsEquiv n).measurableEmbedding (g := F)

omit [NormedSpace ℝ E] in

theorem integrable_euclideanCons_ae {F : EuclideanSpace ℝ (Fin (n + 1)) → E}
    (hF : Integrable F) :
    ∀ᵐ t : ℝ, Integrable (fun y : EuclideanSpace ℝ (Fin n) => F (euclideanCons t y)) :=
  (integrable_euclideanCons_iff.mpr hF).prod_right_ae

theorem integrable_integral_euclideanCons {F : EuclideanSpace ℝ (Fin (n + 1)) → E}
    (hF : Integrable F) :
    Integrable (fun t : ℝ => ∫ y : EuclideanSpace ℝ (Fin n), F (euclideanCons t y)) :=
  (integrable_euclideanCons_iff.mpr hF).integral_prod_left

theorem integral_eq_integral_euclideanCons {F : EuclideanSpace ℝ (Fin (n + 1)) → E}
    (hF : Integrable F) :
    (∫ x, F x) = ∫ t : ℝ, ∫ y : EuclideanSpace ℝ (Fin n), F (euclideanCons t y) := by
  calc
    (∫ x, F x) = ∫ p : ℝ × EuclideanSpace ℝ (Fin n), F (euclideanCons p.1 p.2) := by
      simpa using ((volumePreserving_euclideanConsEquiv n).integral_comp' F).symm
    _ = _ := integral_prod _ (integrable_euclideanCons_iff.mpr hF)

theorem setIntegral_eq_integral_euclideanCons
    {F : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hs : MeasurableSet s) (hF : IntegrableOn F s) :
    (∫ x in s, F x) =
      ∫ t : ℝ, ∫ y in euclideanCons t ⁻¹' s, F (euclideanCons t y) := by
  rw [← integral_indicator hs, integral_eq_integral_euclideanCons
    (hF.integrable_indicator hs)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← integral_indicator (hs.preimage (measurable_euclideanCons t))]
  rfl

omit [NormedSpace ℝ E] in

theorem integrableOn_euclideanCons_ae
    {F : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hs : MeasurableSet s) (hF : IntegrableOn F s) :
    ∀ᵐ t : ℝ, IntegrableOn (fun y => F (euclideanCons t y)) (euclideanCons t ⁻¹' s) := by
  filter_upwards [integrable_euclideanCons_ae (hF.integrable_indicator hs)] with t ht
  rw [← integrable_indicator_iff (hs.preimage (measurable_euclideanCons t))]
  exact ht

theorem integrable_setIntegral_euclideanCons
    {F : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hs : MeasurableSet s) (hF : IntegrableOn F s) :
    Integrable (fun t : ℝ => ∫ y in euclideanCons t ⁻¹' s, F (euclideanCons t y)) := by
  have h := integrable_integral_euclideanCons (hF.integrable_indicator hs)
  convert h using 1
  funext t
  rw [← integral_indicator (hs.preimage (measurable_euclideanCons t))]
  rfl

end Poincare.Coarea
