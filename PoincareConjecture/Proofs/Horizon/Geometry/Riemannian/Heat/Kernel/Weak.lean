import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.TimeDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [IsManifold (𝓡 n) ∞ M] in
private lemma positive_time_germ {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {t : ℝ} (ht : 0 < t) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x) :=
  hF.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)



theorem hasDerivAt_integral_test_mul
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {φ : M → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, φ x * F (s, x) ∂g.volumeMeasure)
      (∫ x, φ x * deriv (fun s => F (s, x)) t ∂g.volumeMeasure) t := by
  have hFc (s : ℝ) (hs : 0 < s) : Continuous (fun x => F (s, x)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (positive_time_germ hF hs x).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id))
  have hdc : ContinuousOn
      (fun p : ℝ × M => φ p.2 * deriv (fun s => F (s, p.2)) p.1)
      (Ioi 0 ×ˢ univ) := by
    intro p hp
    exact ((hφ.continuousAt.comp continuousAt_snd).mul
      (Poincare.Manifold.contMDiffAt_deriv_time
        (positive_time_germ hF hp.1 p.2)).continuousAt).continuousWithinAt
  have hball : Metric.closedBall t (t / 2) ⊆ Ioi (0 : ℝ) := by
    intro s hs
    have h := (abs_le.mp (show |s - t| ≤ t / 2 from by simpa [Real.dist_eq] using hs)).1
    change 0 < s
    linarith
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t (t / 2)).prod hφc.isCompact).exists_bound_of_continuousOn
    (hdc.mono (prod_mono hball (subset_univ _)))
  have hb : Integrable ((tsupport φ).indicator (fun _ : M => C)) g.volumeMeasure :=
    (integrableOn_const hφc.isCompact.measure_ne_top).integrable_indicator
      (isClosed_tsupport φ).measurableSet
  have hdt : Continuous (fun x => φ x * deriv (fun s => F (s, x)) t) := by
    rw [← continuousOn_univ]
    exact hdc.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨ht, mem_univ x⟩)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := g.volumeMeasure)
    (F := fun s x => φ x * F (s, x))
    (F' := fun s x => φ x * deriv (fun r => F (r, x)) s)
    (Metric.closedBall_mem_nhds t (by positivity : 0 < t / 2))
    ?_ ?_ hdt.aestronglyMeasurable ?_ hb ?_).2
  · filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact (hφ.mul (hFc s hs)).aestronglyMeasurable
  · exact (hφ.mul (hFc t ht)).integrable_of_hasCompactSupport hφc.mul_right
  · filter_upwards [] with x
    intro s hs
    by_cases hx : x ∈ tsupport φ
    · simpa only [indicator_of_mem hx] using hC (s, x) ⟨hs, hx⟩
    · simp [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  · filter_upwards [] with x
    intro s hs
    have hd := ((positive_time_germ hF (hball hs) x).comp s
      (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.differentiableAt (by simp)
    exact hd.hasDerivAt.const_mul (φ x)



theorem hasDerivAt_integral_test_mul_of_heatEquation_on_tsupport [PreconnectedSpace M]
    (D : LeviCivitaData g) {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t)
    (hheat : ∀ x ∈ tsupport φ, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t) :
    HasDerivAt (fun s => ∫ x, φ x * F (s, x) ∂g.volumeMeasure)
      (∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure) t := by
  have h := hasDerivAt_integral_test_mul (g := g) hF hφ.continuous hφc ht
  have heq : (∫ x, φ x * deriv (fun s => F (s, x)) t ∂g.volumeMeasure) =
      ∫ x, φ x * D.laplacian (fun y => F (t, y)) x ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · rw [(hheat x hx).deriv]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [heq] at h
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y)) :=
    fun x => (positive_time_germ hF ht x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  rw [D.integral_mul_laplacian_comm_of_hasCompactSupport_left hφ hs hφc] at h
  exact h



theorem hasDerivAt_integral_test_mul_of_heatEquation [PreconnectedSpace M]
    (D : LeviCivitaData g) {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, φ x * F (s, x) ∂g.volumeMeasure)
      (∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure) t :=
  D.hasDerivAt_integral_test_mul_of_heatEquation_on_tsupport hF hφ hφc ht
    (fun x _ => hheat t ht x)



theorem integral_test_mul_heat_sub_on_tsupport [PreconnectedSpace M]
    (D : LeviCivitaData g) {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hheat : ∀ t ∈ Icc a b, ∀ x ∈ tsupport φ, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t) :
    (∫ x, φ x * F (b, x) ∂g.volumeMeasure) -
        (∫ x, φ x * F (a, x) ∂g.volumeMeasure) =
      ∫ t in a..b, ∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure := by
  have hi : ContinuousOn (fun t => ∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure)
      (Icc a b) := by
    apply continuousOn_integral_of_compact_support hφc.isCompact
    · exact (hF.continuousOn.mono (prod_mono (fun t ht => ha.trans_le ht.1) Subset.rfl)).mul
        ((D.continuous_laplacian hφ).comp continuous_snd).continuousOn
    · intro t x _ hx
      simp [D.laplacian_eq_zero_of_notMem_tsupport hx]
  apply (intervalIntegral.integral_eq_sub_of_hasDerivAt ?_
    (hi.intervalIntegrable_of_Icc hab)).symm
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact D.hasDerivAt_integral_test_mul_of_heatEquation_on_tsupport hF hφ hφc
    (ha.trans_le ht.1) (hheat t ht)



theorem integral_test_mul_heat_sub [PreconnectedSpace M]
    (D : LeviCivitaData g) {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, φ x * F (b, x) ∂g.volumeMeasure) -
        (∫ x, φ x * F (a, x) ∂g.volumeMeasure) =
      ∫ t in a..b, ∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure :=
  D.integral_test_mul_heat_sub_on_tsupport hF hφ hφc ha hab
    (fun t ht x _ => hheat t (ha.trans_le ht.1) x)

end PoincareConjecture.LeviCivitaData
