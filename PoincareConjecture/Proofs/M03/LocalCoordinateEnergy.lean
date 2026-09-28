import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false

open scoped ContDiff Topology
open MeasureTheory Set

namespace PoincareConjecture.Proofs.M03

theorem continuousOn_local_coordinate_energy
    {n : ℕ} {J : Set ℝ} (hJ : IsCompact J)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {F : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContinuousOn F (J ×ˢ V))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ V) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ContinuousOn (fun t : ℝ => ∫ x, (φ x * F (t, x)) ^ 2) J := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  let H : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x => (φ x * F (t, x)) ^ 2
  have hHV : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => H p.1 p.2)
      (J ×ˢ V) := ((hφ.comp continuous_snd).continuousOn.mul hF).pow 2
  have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => H p.1 p.2)
      (J ×ˢ Set.univ) := by
    intro p hp
    by_cases hx : p.2 ∈ tsupport φ
    · apply (hHV p ⟨hp.1, hφV hx⟩).mono_of_mem_nhdsWithin
      have hv : {q : ℝ × EuclideanSpace ℝ (Fin n) | q.2 ∈ V} ∈ 𝓝 p :=
        continuous_snd.continuousAt (hV.mem_nhds (hφV hx))
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hv] with q hq hqV
      exact ⟨hq.1, hqV⟩
    · have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin n) => H q.1 q.2) =ᶠ[𝓝 p]
          (fun _ => 0) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
          continuous_snd.continuousAt] with q hq
        change φ q.2 = 0 at hq
        simp [H, hq]
      exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt
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

theorem hasDerivAt_local_coordinate_energy
    {n : ℕ} {I : Set ℝ} (hI : IsOpen I)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {F : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiffOn ℝ 1 F (I ×ˢ V))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ V) {t : ℝ} (ht : t ∈ I) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    HasDerivAt (fun s : ℝ => ∫ x, (φ x * F (s, x)) ^ 2)
      (∫ x, 2 * φ x ^ 2 * F (t, x) * fderiv ℝ F (t, x) (1, 0)) t := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  let H : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun s x => (φ x * F (s, x)) ^ 2
  let D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun s x => 2 * φ x ^ 2 * F (s, x) * fderiv ℝ F (s, x) (1, 0)
  have hopen : IsOpen (I ×ˢ V) := hI.prod hV
  have hpatch : ∀ G : ℝ × EuclideanSpace ℝ (Fin n) → ℝ,
      ContinuousOn G (I ×ˢ V) → (∀ p, p.2 ∉ tsupport φ → G p = 0) →
      ContinuousOn G (I ×ˢ Set.univ) := by
    intro G hG hzero p hp
    by_cases hx : p.2 ∈ tsupport φ
    · exact (hG.continuousAt (hopen.mem_nhds ⟨hp.1, hφV hx⟩)).continuousWithinAt
    · apply ContinuousAt.continuousWithinAt
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt
        ((isClosed_tsupport φ).isOpen_compl.mem_nhds hx)] with q hq
      exact hzero q hq
  have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => H p.1 p.2)
      (I ×ˢ Set.univ) := hpatch _
    (((hφ.comp continuous_snd).continuousOn.mul hF.continuousOn).pow 2)
    (fun p hp => by simp [H, image_eq_zero_of_notMem_tsupport hp])
  have hD : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => D p.1 p.2)
      (I ×ˢ Set.univ) := hpatch _
    (((continuousOn_const.mul ((hφ.comp continuous_snd).continuousOn.pow 2)).mul
      hF.continuousOn).mul
      ((hF.continuousOn_fderiv_of_isOpen hopen le_rfl).clm_apply continuousOn_const))
    (fun p hp => by simp [D, image_eq_zero_of_notMem_tsupport hp])
  have hslice : ∀ s ∈ I, Continuous (H s) := fun s hs =>
    hH.comp_continuous (.prodMk_right s) (fun x => ⟨hs, mem_univ x⟩)
  have hcompact : HasCompactSupport (H t) :=
    (hφc.mul_right (f' := fun x => F (t, x))).comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hdiff : ∀ s ∈ I, ∀ x, HasDerivAt (fun r => H r x) (D s x) s := by
    intro s hs x
    by_cases hx : x ∈ V
    · have hFd : DifferentiableAt ℝ F (s, x) :=
        (hF.differentiableOn (by decide)).differentiableAt (hopen.mem_nhds ⟨hs, hx⟩)
      have hsF : HasDerivAt (fun r : ℝ => F (r, x))
          (fderiv ℝ F (s, x) (1, 0)) s := by
        simpa using! (hFd.hasFDerivAt.comp s
          ((hasDerivAt_id s).hasFDerivAt.prodMk (hasDerivAt_const s x).hasFDerivAt)).hasDerivAt
      convert! (hsF.const_mul (φ x)).pow 2 using 1
      ring
    · have hxφ : x ∉ tsupport φ := fun h => hx (hφV h)
      simpa [H, D, image_eq_zero_of_notMem_tsupport hxφ] using hasDerivAt_const s (0 : ℝ)
  obtain ⟨r, hr, hri⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t r).prod hφc).exists_bound_of_continuousOn
    (hD.mono (Set.prod_mono hri (subset_univ _)))
  have hbound : Integrable ((tsupport φ).indicator (fun _ => max C 0)) :=
    (integrableOn_const (C := max C 0) hφc.measure_ne_top).integrable_indicator
      (isClosed_tsupport φ).measurableSet
  change HasDerivAt (fun s : ℝ => ∫ x, H s x) (∫ x, D t x) t
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := H) (F' := D) (bound := (tsupport φ).indicator (fun _ => max C 0))
    (Metric.closedBall_mem_nhds t hr) ?_ ?_ ?_ ?_ hbound ?_).2
  · filter_upwards [hI.mem_nhds ht] with s hs
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
    exact hdiff s (hri hs) x

theorem local_coordinate_energy_eq_zero_iff
    {n : ℕ} {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {f φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContinuousOn f V) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    (∫ x, (φ x * f x) ^ 2) = 0 ↔ ∀ x, φ x * f x = 0 := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  have hweighted : Continuous (fun x => φ x * f x) :=
    (hφ.continuousOn.mul hf).continuous_of_tsupport_subset hV
      (tsupport_mul_subset_left.trans hφV)
  have hcont : Continuous (fun x => (φ x * f x) ^ 2) := hweighted.pow 2
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
