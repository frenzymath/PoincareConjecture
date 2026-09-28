import PoincareConjecture.Proofs.M08.WeakEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff

namespace PoincareConjecture.M08

theorem exists_finite_weak_subsequence {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, TopologicalSpace.SeparableSpace (H i)]
    (v : ∀ i, ℕ → H i) (C : ι → ℝ) (hbound : ∀ i k, ‖v i k‖ ≤ C i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ∀ i, H i,
      ∀ i, ‖w i‖ ≤ C i ∧ ∀ l : H i →L[ℝ] ℝ,
        Tendsto (fun k ↦ l (v i (φ k))) atTop (𝓝 (l (w i))) := by
  classical
  have hfinite (s : Finset ι) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ s, ∃ w : H i, ‖w‖ ≤ C i ∧ ∀ l : H i →L[ℝ] ℝ,
        Tendsto (fun k ↦ l (v i (φ k))) atTop (𝓝 (l w)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨φ, hφ, hold⟩ := ih
      obtain ⟨w, ψ, hw, hψ, hweak⟩ :=
        exists_weak_subsequence (fun k ↦ v i (φ k)) (C i) (fun k ↦ hbound i (φ k))
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨w, hw, hweak⟩
      · obtain ⟨z, hz, hlim⟩ := hold j hj
        exact ⟨z, hz, fun l ↦ (hlim l).comp hψ.tendsto_atTop⟩
  obtain ⟨φ, hφ, hlim⟩ := hfinite Finset.univ
  choose w hw using fun i ↦ hlim i (Finset.mem_univ i)
  exact ⟨φ, hφ, w, hw⟩

variable {E : Type*} [NormedAddCommGroup E]

section SmoothPrimitive

variable [NormedSpace ℝ E] [CompleteSpace E]

theorem smooth_primitive_fixed_endpoints {a b : ℝ} (hab : a < b)
    (u₀ u₁ : E) (q : ℝ → E) (hq : ContDiff ℝ ∞ q) :
    ∃ f : ℝ → E, ContDiff ℝ ∞ f ∧ f a = u₀ ∧ f b = u₁ ∧
      ∀ s, HasDerivAt f
        (q s + (b - a)⁻¹ • (u₁ - u₀ - ∫ r in a..b, q r)) s := by
  let c : E := (b - a)⁻¹ • (u₁ - u₀ - ∫ r in a..b, q r)
  let d : ℝ → E := fun s ↦ q s + c
  let f : ℝ → E := fun s ↦ u₀ + ∫ r in a..s, d r
  have hd : ContDiff ℝ ∞ d := hq.add contDiff_const
  have hdint : ∀ s t : ℝ, IntervalIntegrable d volume s t := by
    intro s t
    exact (hd.continuous.intervalIntegrable s t)
  have hfderiv (s : ℝ) : HasDerivAt f (d s) s := by
    dsimp only [f]
    exact (intervalIntegral.integral_hasDerivAt_right (hdint a s)
      hd.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hd.continuous.continuousAt).const_add u₀
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun s ↦ (hfderiv s).differentiableAt, ?_⟩
    rw [show deriv f = d by
      funext s
      exact (hfderiv s).deriv]
    exact hd
  have hfa : f a = u₀ := by
    simp only [f, intervalIntegral.integral_same, add_zero]
  have hfb : f b = u₁ := by
    dsimp only [f, d, c]
    rw [intervalIntegral.integral_add (hq.continuous.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const,
      smul_inv_smul₀ (ne_of_gt (sub_pos.mpr hab))]
    abel
  refine ⟨f, hf, hfa, hfb, ?_⟩
  intro s
  simpa only [d, c] using hfderiv s

end SmoothPrimitive

variable [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable abbrev ChartL2 (E : Type*) [NormedAddCommGroup E] (a b : ℝ) :=
  Lp E 2 (volume.restrict (Icc a b))

theorem chartL2_intervalIntegrable {a b : ℝ} (hab : a ≤ b) (v : ChartL2 E a b) :
    IntervalIntegrable v volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact MemLp.integrable (by norm_num) (Lp.memLp v)

theorem chart_primitive_of_deriv {a b : ℝ} {u d : ℝ → E}
    (hu : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt u (d t) t)
    (hLp : MemLp d 2 (volume.restrict (Icc a b))) {t : ℝ} (ht : t ∈ Icc a b) :
    u t = u a + ∫ s in a..t, (hLp.toLp d) s := by
  have hint : IntervalIntegrable d volume a t := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
    exact IntegrableOn.mono_set (MemLp.integrable (by norm_num) hLp)
      (Icc_subset_Icc_right ht.2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hu.mono (Icc_subset_Icc_right ht.2))
    (fun s hs ↦ hd s ⟨hs.1, hs.2.trans_le ht.2⟩) hint
  have heq : (∫ s in a..t, (hLp.toLp d) s) = ∫ s in a..t, d s := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    exact ae_mono (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)) le_rfl) hLp.coeFn_toLp
  rw [heq, hFTC, add_comm, sub_add_cancel]

private theorem chart_integral_as_setIntegral {a b t : ℝ} (ht : t ∈ Icc a b)
    (v : ChartL2 E a b) :
    (∫ s in Icc a t, v s ∂volume.restrict (Icc a b)) = ∫ s in a..t, v s := by
  rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc_right ht.2),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1]

theorem chart_primitive_of_weak_limit {a b : ℝ}
    (u : ℕ → ℝ → E) (g : ℝ → E) (v : ℕ → ChartL2 E a b) (w : ChartL2 E a b)
    (hprimitive : ∀ k t, t ∈ Icc a b → u k t = u k a + ∫ s in a..t, v k s)
    (hpoint : ∀ t ∈ Icc a b, Tendsto (fun k ↦ u k t) atTop (𝓝 (g t)))
    (hweak : ∀ l : ChartL2 E a b →L[ℝ] ℝ,
      Tendsto (fun k ↦ l (v k)) atTop (𝓝 (l w))) {t : ℝ} (ht : t ∈ Icc a b) :
    g t = g a + ∫ s in a..t, w s := by
  apply ext_inner_left ℝ
  intro z
  let test : ChartL2 E a b :=
    indicatorConstLp 2 (s := Icc a t) measurableSet_Icc (measure_ne_top _ _) z
  have htest (q : ChartL2 E a b) :
      inner ℝ test q = inner ℝ z (∫ s in a..t, q s) := by
    dsimp only [test]
    rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ]
    rw [chart_integral_as_setIntegral ht q]
  have hw := hweak (innerSL ℝ test)
  change Tendsto (fun k ↦ inner ℝ test (v k)) atTop (𝓝 (inner ℝ test w)) at hw
  simp only [htest] at hw
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hsum := (Filter.Tendsto.inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := z)) (hpoint a ha)).add hw
  have hsum' : Tendsto (fun k ↦ inner ℝ z (u k t)) atTop
      (𝓝 (inner ℝ z (g a + ∫ s in a..t, w s))) := by
    simpa only [inner_add_right, hprimitive _ _ ht] using hsum
  exact tendsto_nhds_unique
    (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (hpoint t ht)) hsum'

theorem chart_primitive_ae_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → E) (w : ChartL2 E a b)
    (hprimitive : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, w r) :
    ∀ᵐ s ∂volume.restrict (Icc a b), HasDerivAt u (w s) s := by
  have hFTC := (chartL2_intervalIntegrable hab w).ae_hasDerivAt_integral
  rw [uIcc_of_le hab] at hFTC
  have hmem : ∀ᵐ s ∂volume.restrict (Icc a b), s ∈ Ioo a b := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [ae_restrict_of_ae hFTC, hmem] with s hs hsI
  have hd := (hs (Ioo_subset_Icc_self hsI) a ⟨le_rfl, hab⟩).const_add (u a)
  apply hd.congr_of_eventuallyEq
  exact eventually_of_mem (Ioo_mem_nhds hsI.1 hsI.2)
    (fun r hr ↦ hprimitive r (Ioo_subset_Icc_self hr))

end PoincareConjecture.M08
