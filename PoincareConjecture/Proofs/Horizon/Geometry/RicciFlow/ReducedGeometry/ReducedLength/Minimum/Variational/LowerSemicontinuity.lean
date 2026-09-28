import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.QuadraticEnergy
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def integratedFormMap (μ : Measure A)
    (B : Lp (E →L[ℝ] E →L[ℝ] ℝ) ∞ μ) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).lpPairing μ 2 2).comp
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)).holderL μ ∞ 2 2 B)

set_option maxHeartbeats 800000 in

theorem integratedFormMap_apply {μ : Measure A}
    (B : Lp (E →L[ℝ] E →L[ℝ] ℝ) ∞ μ) (v w : Lp E 2 μ) :
    integratedFormMap μ B v w = ∫ t, B t (v t) (w t) ∂μ := by
  simp only [integratedFormMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.holderL_apply_apply]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E) (G := E →L[ℝ] ℝ) (r := 2)
    (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)) B v]
    with t ht
  exact congrArg (fun l : E →L[ℝ] ℝ => l (w t)) ht

theorem integratedFormMap_toLp {μ : Measure A}
    {B : A → E →L[ℝ] E →L[ℝ] ℝ} (hB : MemLp B ∞ μ) (v w : Lp E 2 μ) :
    integratedFormMap μ (hB.toLp B) v w = ∫ t, B t (v t) (w t) ∂μ := by
  rw [integratedFormMap_apply]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (E := E →L[ℝ] E →L[ℝ] ℝ) hB] with t ht
  rw [ht]

set_option maxHeartbeats 800000 in

theorem integratedFormMap_norm_le (μ : Measure A)
    (B : Lp (E →L[ℝ] E →L[ℝ] ℝ) ∞ μ) :
    ‖integratedFormMap (E := E) μ B‖ ≤ ‖B‖ := by
  have hI : ‖(L1.integralCLM' ℝ : Lp ℝ 1 μ →L[ℝ] ℝ)‖ ≤ 1 :=
    L1.norm_Integral_le_one
  have hP : ‖(ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).lpPairing μ 2 2‖ ≤ 1 := by
    unfold ContinuousLinearMap.lpPairing
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    calc
      _ ≤ 1 * 1 := mul_le_mul
        ((ContinuousLinearMap.norm_postcomp_le (E := Lp E 2 μ)
          (L1.integralCLM' ℝ : Lp ℝ 1 μ →L[ℝ] ℝ)).trans hI)
        ((ContinuousLinearMap.norm_holderL_le (μ := μ) (p := 2) (q := 2) (r := 1)
          (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ))).trans ContinuousLinearMap.norm_id_le)
        (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  let S := ContinuousLinearMap.holderL (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E) (G := E →L[ℝ] ℝ)
    μ ∞ 2 2 (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hS : ‖S B‖ ≤ ‖B‖ := by
    apply (S B).opNorm_le_bound (norm_nonneg B)
    intro v
    have h := ContinuousLinearMap.norm_holder_apply_apply_le (𝕜 := ℝ)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E) (G := E →L[ℝ] ℝ) (r := 2)
      (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)) B v
    have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hid (norm_nonneg B)) (norm_nonneg v)
    exact h.trans (by simpa only [one_mul] using hmul)
  change ‖((ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).lpPairing μ 2 2).comp
    (S B)‖ ≤ _
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1 * ‖B‖ := mul_le_mul hP hS
      (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ = ‖B‖ := one_mul _

theorem lpTop_norm_le_of_bound {F : Type*} [NormedAddCommGroup F] {μ : Measure A}
    {f : A → F} (hf : MemLp f ∞ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hbound)).trans_eq (ENNReal.toReal_ofReal hC)

theorem integratedForm_nonneg {μ : Measure A}
    {B : A → E →L[ℝ] E →L[ℝ] ℝ} (hB : MemLp B ∞ μ)
    (hpos : ∀ᵐ t ∂μ, ∀ z, 0 ≤ B t z z) (v : Lp E 2 μ) :
    0 ≤ integratedFormMap μ (hB.toLp B) v v := by
  rw [integratedFormMap_apply]
  apply integral_nonneg_of_ae
  filter_upwards [MemLp.coeFn_toLp (E := E →L[ℝ] E →L[ℝ] ℝ) hB, hpos] with t hrep ht
  rw [hrep]
  exact ht (v t)

theorem integratedForm_sub_norm_le {μ : Measure A}
    {B D : A → E →L[ℝ] E →L[ℝ] ℝ} (hB : MemLp B ∞ μ) (hD : MemLp D ∞ μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (herror : ∀ᵐ t ∂μ, ‖B t - D t‖ ≤ δ) :
    ‖integratedFormMap μ (hB.toLp B) - integratedFormMap μ (hD.toLp D)‖ ≤ δ := by
  have heq : integratedFormMap μ (hB.toLp B) - integratedFormMap μ (hD.toLp D) =
      integratedFormMap μ ((hB.sub hD).toLp (B - D)) := by
    rw [MemLp.toLp_sub hB hD]
    simp only [integratedFormMap, map_sub, ContinuousLinearMap.comp_sub]
  rw [heq]
  exact (integratedFormMap_norm_le μ _).trans (lpTop_norm_le_of_bound _ hδ herror)

theorem continuousOn_memLp_top_Icc {V : Type*} [NormedAddCommGroup V]
    {a b : ℝ} {f : ℝ → V} (hf : ContinuousOn f (Set.Icc a b)) :
    MemLp f ∞ (volume.restrict (Set.Icc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply memLp_top_of_bound (hf.aestronglyMeasurable measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hC s hs

theorem integratedForm_tendsto_of_uniform {a b : ℝ}
    (B : ℕ → ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ k, MemLp (B k) ∞ (volume.restrict (Set.Icc a b)))
    (hD : MemLp D ∞ (volume.restrict (Set.Icc a b)))
    (hlim : TendstoUniformlyOn B D atTop (Set.Icc a b)) :
    Tendsto (fun k => ‖integratedFormMap _ ((hB k).toLp (B k)) -
      integratedFormMap _ (hD.toLp D)‖) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hpair : TendstoUniformlyOn (fun k s => (D s, B k s))
      (fun s => (D s, D s)) atTop (Set.Icc a b) := by
    intro U hU
    obtain ⟨u, hu, v', hv', huv⟩ := entourageProd_subset hU
    filter_upwards [hlim v' hv'] with k hk
    intro s hs
    apply huv
    exact ⟨refl_mem_uniformity hu, hk s hs⟩
  have hdiff : TendstoUniformlyOn (fun k s => B k s - D s)
      (fun _ : ℝ => (0 : E →L[ℝ] E →L[ℝ] ℝ)) atTop (Set.Icc a b) := by
    simpa only [Function.comp_def, sub_self] using
      (uniformContinuous_snd.sub uniformContinuous_fst).comp_tendstoUniformlyOn hpair
  have hnormlim : TendstoUniformlyOn (fun k s => ‖B k s - D s‖)
      (fun _ : ℝ => (0 : ℝ)) atTop (Set.Icc a b) := by
    simpa only [Function.comp_def, ContinuousLinearMap.opNorm_zero] using
      (uniformContinuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).comp_tendstoUniformlyOn hdiff
  have hlim' : ∀ᶠ k in atTop, ∀ s ∈ Set.Icc a b,
      ‖B k s - D s‖ < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)] using
      (Metric.tendstoUniformlyOn_iff.mp hnormlim) (ε / 2) (half_pos hε)
  filter_upwards [hlim'] with k hk
  have hnorm : ‖integratedFormMap _ ((hB k).toLp (B k)) -
      integratedFormMap _ (hD.toLp D)‖ ≤ ε / 2 :=
    integratedForm_sub_norm_le (hB k) hD (half_pos hε).le (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact (hk s hs).le)
  simpa only [Real.dist_eq, sub_zero,
    abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)] using
    (lt_of_le_of_lt hnorm (half_lt_self hε))

theorem finite_integral_action_le_of_weak_limit
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (a b : ι → ℝ)
    (B : ∀ i, ℕ → ℝ → V i →L[ℝ] V i →L[ℝ] ℝ)
    (D : ∀ i, ℝ → V i →L[ℝ] V i →L[ℝ] ℝ)
    (hB : ∀ i k, MemLp (B i k) ∞ (volume.restrict (Set.Icc (a i) (b i))))
    (hD : ∀ i, MemLp (D i) ∞ (volume.restrict (Set.Icc (a i) (b i))))
    (hpos : ∀ i, ∀ᵐ s ∂volume.restrict (Set.Icc (a i) (b i)), ∀ z, 0 ≤ D i s z z)
    (hcoeff : ∀ i, TendstoUniformlyOn (B i) (D i) atTop (Set.Icc (a i) (b i)))
    (v : ∀ i, ℕ → Lp (V i) 2 (volume.restrict (Set.Icc (a i) (b i))))
    (w : ∀ i, Lp (V i) 2 (volume.restrict (Set.Icc (a i) (b i))))
    (C : ι → ℝ) (hbound : ∀ i k, ‖v i k‖ ≤ C i)
    (hweak : ∀ i, ∀ l : Lp (V i) 2 (volume.restrict (Set.Icc (a i) (b i))) →L[ℝ] ℝ,
      Tendsto (fun k => l (v i k)) atTop (𝓝 (l (w i))))
    (potential action : ℕ → ℝ) (P L : ℝ)
    (hpotential : Tendsto potential atTop (𝓝 P)) (haction : Tendsto action atTop (𝓝 L))
    (henergy : ∀ k,
      (∑ i, ∫ s, B i k s (v i k s) (v i k s) ∂volume.restrict (Set.Icc (a i) (b i))) +
        potential k ≤ action k) :
    (∑ i, ∫ s, D i s (w i s) (w i s) ∂volume.restrict (Set.Icc (a i) (b i))) + P ≤ L := by
  let Q i := integratedFormMap _ ((hD i).toLp (D i))
  let Qk i k := integratedFormMap _ ((hB i k).toLp (B i k))
  have hQ i : Tendsto (fun k => ‖Qk i k - Q i‖) atTop (𝓝 (0 : ℝ)) :=
    integratedForm_tendsto_of_uniform (B i) (D i) (hB i) (hD i) (hcoeff i)
  have htotal := finite_quadratic_action_le v w C
    (fun i => (norm_nonneg (v i 0)).trans (hbound i 0)) hbound hweak Q Qk
    (fun i z => integratedForm_nonneg (hD i) (hpos i) z) hQ
    potential action P L hpotential haction (by
      intro k
      simpa only [Qk, integratedFormMap_toLp] using henergy k)
  simpa only [Q, integratedFormMap_toLp] using htotal

end PoincareConjecture.ReducedLengthMinimum.Variational
