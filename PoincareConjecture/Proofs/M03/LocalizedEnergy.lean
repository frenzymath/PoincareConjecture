import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.Calculus.ParametricIntegral










set_option autoImplicit false

open scoped ContDiff Topology
open MeasureTheory Set

namespace PoincareConjecture.Proofs.M03

theorem continuousOn_localized_scalar_energy
    {n : ℕ} {J : Set ℝ} (hJ : IsCompact J)
    {F : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContinuousOn F (J ×ˢ Set.univ))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ContinuousOn (fun t : ℝ => ∫ x, (φ x * F (t, x)) ^ 2) J := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  let H : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x => (φ x * F (t, x)) ^ 2
  have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => H p.1 p.2)
      (J ×ˢ Set.univ) :=
    ((hφ.comp continuous_snd).continuousOn.mul hF).pow 2
  obtain ⟨C, hC⟩ := (hJ.prod hφc).exists_bound_of_continuousOn
    (hH.mono (Set.prod_mono_right (subset_univ _)))
  have hbound : Integrable ((tsupport φ).indicator (fun _ => max C 0)) :=
    (integrableOn_const (C := max C 0) hφc.measure_ne_top).integrable_indicator
      (isClosed_tsupport φ).measurableSet
  change ContinuousOn (fun t : ℝ => ∫ x, H t x) J
  apply continuousOn_of_dominated (bound := (tsupport φ).indicator (fun _ => max C 0))
  · intro t ht
    exact (hH.comp_continuous (.prodMk_right t) (fun x => ⟨ht, mem_univ x⟩)).aestronglyMeasurable
  · intro t ht
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
      exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
    · simp [H, indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  · exact hbound
  · filter_upwards with x
    exact hH.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ x⟩)

theorem hasDerivAt_localized_scalar_energy
    {n : ℕ} {U : Set ℝ} (hU : IsOpen U)
    {F : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiffOn ℝ 1 F (U ×ˢ Set.univ))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {t : ℝ} (ht : t ∈ U) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    HasDerivAt (fun s : ℝ => ∫ x, (φ x * F (s, x)) ^ 2)
      (∫ x, 2 * φ x ^ 2 * F (t, x) * fderiv ℝ F (t, x) (1, 0)) t := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  let H : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun s x => (φ x * F (s, x)) ^ 2
  let D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun s x => 2 * φ x ^ 2 * F (s, x) * fderiv ℝ F (s, x) (1, 0)
  have hopen : IsOpen (U ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) :=
    hU.prod isOpen_univ
  have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => H p.1 p.2)
      (U ×ˢ Set.univ) :=
    ((hφ.comp continuous_snd).continuousOn.mul hF.continuousOn).pow 2
  have hD : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => D p.1 p.2)
      (U ×ˢ Set.univ) :=
    ((continuousOn_const.mul ((hφ.comp continuous_snd).continuousOn.pow 2)).mul
      hF.continuousOn).mul
      ((hF.continuousOn_fderiv_of_isOpen hopen le_rfl).clm_apply continuousOn_const)
  have hslice : ∀ s ∈ U, Continuous (H s) := fun s hs =>
    hH.comp_continuous (.prodMk_right s) (fun x => ⟨hs, mem_univ x⟩)
  have hcompact : HasCompactSupport (H t) :=
    (hφc.mul_right (f' := fun x => F (t, x))).comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hdiff : ∀ s ∈ U, ∀ x, HasDerivAt (fun r => H r x) (D s x) s := by
    intro s hs x
    have hFd : DifferentiableAt ℝ F (s, x) :=
      (hF.differentiableOn (by decide)).differentiableAt (hopen.mem_nhds ⟨hs, mem_univ x⟩)
    have hsF : HasDerivAt (fun r : ℝ => F (r, x))
        (fderiv ℝ F (s, x) (1, 0)) s := by
      simpa using! (hFd.hasFDerivAt.comp s
        ((hasDerivAt_id s).hasFDerivAt.prodMk (hasDerivAt_const s x).hasFDerivAt)).hasDerivAt
    convert! (hsF.const_mul (φ x)).pow 2 using 1
    ring
  obtain ⟨r, hr, hru⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ht)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t r).prod hφc).exists_bound_of_continuousOn
    (hD.mono (Set.prod_mono hru (subset_univ _)))
  have hbound : Integrable ((tsupport φ).indicator (fun _ => max C 0)) :=
    (integrableOn_const (C := max C 0) hφc.measure_ne_top).integrable_indicator
      (isClosed_tsupport φ).measurableSet
  change HasDerivAt (fun s : ℝ => ∫ x, H s x) (∫ x, D t x) t
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := H) (F' := D) (bound := (tsupport φ).indicator (fun _ => max C 0))
    (Metric.closedBall_mem_nhds t hr) ?_ ?_ ?_ ?_ hbound ?_).2
  · filter_upwards [hU.mem_nhds ht] with s hs
    exact (hslice s hs).aestronglyMeasurable
  · exact (hslice t ht).integrable_of_hasCompactSupport hcompact
  · exact (hD.comp_continuous (.prodMk_right t) (fun x => ⟨ht, mem_univ x⟩)).aestronglyMeasurable
  · filter_upwards with x
    intro s hs
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
      exact (hC (s, x) ⟨hs, hx⟩).trans (le_max_left _ _)
    · simp [D, indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  · filter_upwards with x
    intro s hs
    exact hdiff s (hru hs) x

theorem localized_scalar_energy_eq_zero_iff
    {n : ℕ} {f φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    (∫ x, (φ x * f x) ^ 2) = 0 ↔ ∀ x, φ x * f x = 0 := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  have hcont : Continuous (fun x => (φ x * f x) ^ 2) := (hφ.mul hf).pow 2
  have hcompact : HasCompactSupport (fun x => (φ x * f x) ^ 2) :=
    (hφc.mul_right (f' := f)).comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  change (∫ x, (φ x * f x) ^ 2) = 0 ↔ ∀ x, φ x * f x = 0
  constructor
  · intro hzero
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (φ x * f x))
      (hcont.integrable_of_hasCompactSupport hcompact)).mp hzero
    have heq := Measure.eq_of_ae_eq hae hcont continuous_const
    intro x
    exact sq_eq_zero_iff.mp (congrFun heq x)
  · intro hzero
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), integral_zero]

end PoincareConjecture.Proofs.M03
