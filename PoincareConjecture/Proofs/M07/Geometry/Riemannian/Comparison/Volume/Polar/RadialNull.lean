import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order















open MeasureTheory Measure Set Metric Module
open scoped ENNReal NNReal

namespace Poincare.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]



instance nullSingletonClass_volumeIoiPow (n : ℕ) :
    NullSingletonClass (Measure.volumeIoiPow n) where
  measure_singleton r := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    simp


def IsRadialGraph (A : Set E) : Prop :=
  ∀ u ∈ sphere (0 : E) 1, ∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ → r₁ • u ∈ A → r₂ • u ∈ A → r₁ = r₂


theorem addHaar_eq_zero_of_isRadialGraph (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : Set E} (hAmeas : MeasurableSet A) (hA0 : (0 : E) ∉ A) (hray : IsRadialGraph A) :
    μ A = 0 := by
  classical

  have hcompl : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton (0 : E)).compl
  set A' : Set ({0}ᶜ : Set E) := ((↑) : ({0}ᶜ : Set E) → E) ⁻¹' A with hA'
  have hA'meas : MeasurableSet A' := hAmeas.preimage measurable_subtype_coe

  set Φ := homeomorphUnitSphereProd E with hΦ
  have hemb : MeasurableEmbedding Φ := Φ.measurableEmbedding
  have hmp : MeasurePreserving Φ (μ.comap ((↑) : ({0}ᶜ : Set E) → E))
      (μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) :=
    Measure.measurePreserving_homeomorphUnitSphereProd μ

  have himg : MeasurableSet (Φ '' A') := hemb.measurableSet_image.2 hA'meas

  have hslice : ∀ u : sphere (0 : E) 1,
      (Prod.mk u ⁻¹' (Φ '' A')).Subsingleton := by
    intro u r₁ hr₁ r₂ hr₂

    have key : ∀ r : Ioi (0 : ℝ), (u, r) ∈ Φ '' A' → (r : ℝ) • (u : E) ∈ A := by
      rintro r ⟨w, hw, hwr⟩
      have hsymm : (Φ.symm (u, r) : E) = (r : ℝ) • (u : E) := by
        simp [hΦ, homeomorphUnitSphereProd_symm_apply_coe]
      have hw' : (w : E) = (r : ℝ) • (u : E) := by
        have : Φ.symm (Φ w) = Φ.symm (u, r) := by rw [hwr]
        rw [Φ.symm_apply_apply] at this
        rw [← hsymm, ← this]
      exact hw' ▸ hw
    have h₁ := key r₁ hr₁
    have h₂ := key r₂ hr₂
    have : (r₁ : ℝ) = (r₂ : ℝ) :=
      hray u u.2 r₁ r₂ (mem_Ioi.1 r₁.2) (mem_Ioi.1 r₂.2) h₁ h₂
    exact Subtype.ext this

  have hprod : (μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) (Φ '' A') = 0 := by
    refine measure_prod_null_of_ae_null himg ?_
    filter_upwards with u
    exact (hslice u).measure_zero _

  have hA'null : (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) A' = 0 := by
    have hpre : Φ ⁻¹' (Φ '' A') = A' := Φ.injective.preimage_image A'
    calc (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) A'
        = (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) (Φ ⁻¹' (Φ '' A')) := by rw [hpre]
      _ = (μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) (Φ '' A') :=
          hmp.measure_preimage_emb hemb _
      _ = 0 := hprod

  have hsub : A ⊆ ({0}ᶜ : Set E) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hA0 hx
  have himage : ((↑) : ({0}ᶜ : Set E) → E) '' A' = A := by
    rw [hA', Subtype.image_preimage_coe, inter_eq_self_of_subset_right hsub]
  rwa [comap_subtype_coe_apply hcompl, himage] at hA'null

end Poincare.VolumeComparison
