import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.MeasureComparison
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace Poincare.HausdorffDensity

theorem measure_image_bounds_of_linear_comparison
    {n : ℕ} {M : Type*} [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : U ⊆ e.source) (hs : s ⊆ U)
    {K : ℝ≥0}
    (hf : ∀ z ∈ U, ∀ w ∈ U, edist (e z) (e w) ≤ (K : ℝ≥0∞) * edist (A z) (A w))
    (hi : ∀ z ∈ U, ∀ w ∈ U, edist (A z) (A w) ≤ (K : ℝ≥0∞) * edist (e z) (e w)) :
    Measure.euclideanHausdorffMeasure n (e '' s) ≤
        (K : ℝ≥0∞) ^ n * (ENNReal.ofReal |A.toContinuousLinearMap.det| * volume s) ∧
      ENNReal.ofReal |A.toContinuousLinearMap.det| * volume s ≤
        (K : ℝ≥0∞) ^ n * Measure.euclideanHausdorffMeasure n (e '' s) := by
  have hvol : Measure.euclideanHausdorffMeasure n (A '' s) =
      ENNReal.ofReal |A.toContinuousLinearMap.det| * volume s := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_image_continuousLinearEquiv]
    rfl
  have hforward : LipschitzOnWith K (e ∘ A.symm) (A '' s) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    simpa using hf z (hs hz) w (hs hw)
  have hinverse : LipschitzOnWith K (A ∘ e.symm) (e '' s) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    simpa only [Function.comp_apply, e.left_inv (hU (hs hz)),
      e.left_inv (hU (hs hw))] using hi z (hs hz) w (hs hw)
  have himage : (e ∘ A.symm) '' (A '' s) = e '' s := by
    rw [← image_comp]
    simp [Function.comp_def]
  have hiimage : (A ∘ e.symm) '' (e '' s) = A '' s := by
    rw [← image_comp]
    apply image_congr
    intro x hx
    simp [Function.comp_def, e.left_inv (hU (hs hx))]
  constructor
  · simpa only [himage, hvol] using euclideanHausdorffMeasure_image_le hforward n
  · simpa only [hiimage, hvol] using euclideanHausdorffMeasure_image_le hinverse n

theorem eventually_density_bounds {X : Type*} [TopologicalSpace X]
    {ρ : X → ℝ} {x : X} (hρ : ContinuousAt ρ x) (hpos : 0 < ρ x)
    {K : ℝ≥0} (hK : 1 < K) :
    ∀ᶠ y in 𝓝 x, ρ x ≤ K * ρ y ∧ ρ y ≤ K * ρ x := by
  have hlt : ρ x < (K : ℝ) * ρ x := by
    exact lt_mul_of_one_lt_left hpos (by exact_mod_cast hK)
  filter_upwards [(continuousAt_const.mul hρ).eventually (lt_mem_nhds hlt),
    hρ.eventually (gt_mem_nhds hlt)] with y hy hy'
  exact ⟨hy.le, hy'.le⟩

theorem map_restrict_symm_apply
    {X M : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (e : OpenPartialHomeomorph X M) (μ : Measure M)
    {s : Set X} (hs : MeasurableSet s) (hse : s ⊆ e.source) :
    ((μ.restrict e.target).map e.symm) s = μ (e '' s) := by
  have hm : AEMeasurable e.symm (μ.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  rw [Measure.map_apply_of_aemeasurable hm hs,
    Measure.restrict_apply' e.open_target.measurableSet,
    e.image_eq_target_inter_inv_preimage hse, inter_comm]

theorem density_integral_bounds
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) {ρ : X → ℝ} {c : ℝ} {K : ℝ≥0}
    (h : ∀ x ∈ s, c ≤ K * ρ x ∧ ρ x ≤ K * c) :
    ENNReal.ofReal c * μ s ≤ (K : ℝ≥0∞) * ∫⁻ x in s, ENNReal.ofReal (ρ x) ∂μ ∧
      (∫⁻ x in s, ENNReal.ofReal (ρ x) ∂μ) ≤ (K : ℝ≥0∞) * (ENNReal.ofReal c * μ s) := by
  constructor
  · calc
      ENNReal.ofReal c * μ s = ∫⁻ _ in s, ENNReal.ofReal c ∂μ := by simp
      _ ≤ ∫⁻ x in s, ENNReal.ofReal (K * ρ x) ∂μ :=
        setLIntegral_mono' hs fun x hx ↦ ENNReal.ofReal_le_ofReal (h x hx).1
      _ = (K : ℝ≥0∞) * ∫⁻ x in s, ENNReal.ofReal (ρ x) ∂μ := by
        simp_rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
        exact lintegral_const_mul' _ _ ENNReal.coe_ne_top
  · calc
      (∫⁻ x in s, ENNReal.ofReal (ρ x) ∂μ) ≤ ∫⁻ _ in s, ENNReal.ofReal (K * c) ∂μ :=
        setLIntegral_mono' hs fun x hx ↦ ENNReal.ofReal_le_ofReal (h x hx).2
      _ = (K : ℝ≥0∞) * (ENNReal.ofReal c * μ s) := by
        simp [ENNReal.ofReal_mul K.coe_nonneg, mul_assoc]

theorem hausdorffMeasure_image_eq_lintegral_of_locally_linear_comparison
    {n : ℕ} {M : Type*} [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : ∀ x ∈ e.source, ContinuousAt ρ x ∧ 0 < ρ x)
    (hlocal : ∀ x ∈ e.source, ∀ K : ℝ≥0, 1 < K →
      ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        |A.toContinuousLinearMap.det| = ρ x ∧
      ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
        (∀ z ∈ U, ∀ w ∈ U, edist (e z) (e w) ≤ (K : ℝ≥0∞) * edist (A z) (A w)) ∧
        (∀ z ∈ U, ∀ w ∈ U, edist (A z) (A w) ≤ (K : ℝ≥0∞) * edist (e z) (e w)))
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) (hse : s ⊆ e.source) :
    Measure.euclideanHausdorffMeasure n (e '' s) =
      ∫⁻ x in s, ENNReal.ofReal (ρ x) := by
  let μ := ((Measure.euclideanHausdorffMeasure n : Measure M).restrict e.target).map e.symm
  let ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
    (fun x ↦ ENNReal.ofReal (ρ x))
  have hμ (t : Set (EuclideanSpace ℝ (Fin n))) (ht : MeasurableSet t)
      (hte : t ⊆ e.source) : μ t = Measure.euclideanHausdorffMeasure n (e '' t) :=
    map_restrict_symm_apply e _ ht hte
  have hν (t : Set (EuclideanSpace ℝ (Fin n))) (ht : MeasurableSet t) :
      ν t = ∫⁻ x in t, ENNReal.ofReal (ρ x) := withDensity_apply _ ht
  rw [← hμ s hs hse, ← hν s hs]
  apply measure_eq_of_locally_approx hs (n + 1)
  intro K hK x hx
  obtain ⟨A, hA, U, hUo, hUx, hUe, hUf, hUi⟩ := hlocal x (hse hx) K hK
  obtain ⟨V, hVsub, hVo, hVx⟩ := mem_nhds_iff.mp
    (eventually_density_bounds (hρ x (hse hx)).1 (hρ x (hse hx)).2 hK)
  refine ⟨U ∩ V, hUo.inter hVo, ⟨hUx, hVx⟩, fun t ht hts ↦ ?_⟩
  have htU : t ⊆ U := fun y hy ↦ (hts hy).1.1
  have htd := density_integral_bounds (μ := volume) ht
    (fun y hy ↦ hVsub (hts hy).1.2)
  have htm := measure_image_bounds_of_linear_comparison e A hUe htU hUf hUi
  rw [hA, ← hμ t ht (htU.trans hUe)] at htm
  rw [← hν t ht] at htd
  constructor
  · calc
      μ t ≤ (K : ℝ≥0∞) ^ n * (ENNReal.ofReal (ρ x) * volume t) := htm.1
      _ ≤ (K : ℝ≥0∞) ^ n * ((K : ℝ≥0∞) * ν t) := mul_le_mul_right htd.1 _
      _ = (K : ℝ≥0∞) ^ (n + 1) * ν t := by rw [pow_succ, mul_assoc]
  · calc
      ν t ≤ (K : ℝ≥0∞) * (ENNReal.ofReal (ρ x) * volume t) := htd.2
      _ ≤ (K : ℝ≥0∞) * ((K : ℝ≥0∞) ^ n * μ t) := mul_le_mul_right htm.2 _
      _ = (K : ℝ≥0∞) ^ (n + 1) * μ t := by rw [pow_succ']; simp only [mul_assoc]

end Poincare.HausdorffDensity
