import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFourierDecoder
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianFourier
import PoincareConjecture.Proofs.M03.Existence.SpectralHeatNative

set_option autoImplicit false

open MeasureTheory AddCircle Filter
open scoped ENNReal Topology

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

omit [Fact (0 < L)] in
private theorem periodicHeatWeight_bound {τ t : ℝ} (hτ : 0 < τ) (ht : τ ≤ t)
    (n : ℤ) :
    Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * t) ≤
      (1 + τ⁻¹) * (1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)) := by
  let a : ℝ := (2 * Real.pi * (n : ℝ) / L) ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  have htpos : 0 < t := lt_of_lt_of_le hτ ht
  have hspos : 0 < Real.sqrt (1 + a) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (1 + a) ≤ 1 + a := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + a by positivity), Real.sqrt_nonneg (1 + a)]
  have he : Real.exp (-a * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hae : a * Real.exp (-a * t) ≤ t⁻¹ := by
    simpa only [abs_of_nonneg (mul_nonneg ha (Real.exp_nonneg _)), mul_comm a t,
      neg_mul, mul_neg] using
      PoincareConjecture.SpectralHeatNative.spectralCoefficient_bound htpos ha
  have hi : t⁻¹ ≤ τ⁻¹ := inv_anti₀ hτ ht
  have hb : Real.sqrt (1 + a) * Real.exp (-a * t) ≤ 1 + τ⁻¹ := by
    calc
      _ ≤ (1 + a) * Real.exp (-a * t) :=
        mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)
      _ = Real.exp (-a * t) + a * Real.exp (-a * t) := by ring
      _ ≤ 1 + τ⁻¹ := add_le_add he (hae.trans hi)
  change Real.exp (-a * t) ≤ (1 + τ⁻¹) * (1 / Real.sqrt (1 + a))
  rw [mul_one_div, le_div_iff₀ hspos]
  simpa only [mul_comm] using hb

theorem memℓp_periodicHeatWeight {t : ℝ} (ht : 0 < t) :
    Memℓp (fun n : ℤ =>
      (Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * t) : ℂ)) 2 := by
  apply ((memℓp_periodic_decayWeight (Fact.out : 0 < L)).const_mul (1 + t⁻¹)).mono
  intro n
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact periodicHeatWeight_bound ht le_rfl n

noncomputable def periodicL2Heat (t : ℝ) (ht : 0 < t) :
    Lp ℂ 2 (haarAddCircle (T := L)) →L[ℂ] C(AddCircle L, ℂ) :=
  (weightedFourier ⟨fun n : ℤ =>
    (Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * t) : ℂ),
    memℓp_periodicHeatWeight ht⟩).comp
      fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem periodicL2Heat_eq_gaussian (t : ℝ) (ht : 0 < t)
    (f : C(AddCircle L, ℂ)) :
    periodicL2Heat t ht (ContinuousMap.toLp 2 haarAddCircle ℂ f) =
      periodicGaussianHeat t f := by
  classical
  let G : C(AddCircle L, ℂ) →L[ℂ] C(AddCircle L, ℂ) :=
    { toLinearMap :=
        { toFun := periodicGaussianHeat t
          map_add' := (periodicGaussianHeat t).map_add
          map_smul' := fun c g => by
            have h := periodicGaussianHeat_comp
              ((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ) t g
            change periodicGaussianHeat t (c • g) = c • periodicGaussianHeat t g at h
            exact h }
      cont := (periodicGaussianHeat t).continuous }
  let A : C(AddCircle L, ℂ) →L[ℂ] C(AddCircle L, ℂ) :=
    (periodicL2Heat t ht).comp (ContinuousMap.toLp 2 haarAddCircle ℂ)
  have hmode (n : ℤ) : A (fourier n) = G (fourier n) := by
    have hc : (fourierBasis (T := L)).repr
        (ContinuousMap.toLp 2 haarAddCircle ℂ (fourier n)) =
        lp.single 2 n (1 : ℂ) := by
      simpa only [coe_fourierBasis] using (fourierBasis (T := L)).repr_self n
    let w : lp (fun _ : ℤ => ℂ) 2 :=
      ⟨fun m : ℤ => (Real.exp (-(2 * Real.pi * (m : ℝ) / L) ^ 2 * t) : ℂ),
        memℓp_periodicHeatWeight ht⟩
    have hs := weightedFourier_hasSum (L := L) w (lp.single 2 n (1 : ℂ))
    have hterms (m : ℤ) : (w m * lp.single (E := fun _ : ℤ => ℂ) 2 n 1 m) •
        (fourier m : C(AddCircle L, ℂ)) =
        if m = n then w n • fourier n else 0 := by
      by_cases hm : m = n
      · subst m
        simp
      · simp [lp.single_apply, hm]
    simp_rw [hterms] at hs
    have heq := hs.unique (hasSum_ite_eq n (w n • (fourier n : C(AddCircle L, ℂ))))
    change weightedFourier _ (fourierBasis.repr
      (ContinuousMap.toLp 2 haarAddCircle ℂ (fourier n))) = periodicGaussianHeat t (fourier n)
    rw [hc, heq]
    simpa only [one_smul, one_mul, w] using
      (periodicGaussianHeat_fourier t ht.le (1 : ℂ) n).symm
  have hAG : A = G := ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top)
    (by rintro g ⟨n, rfl⟩; exact hmode n)
  exact congrArg (fun B : C(AddCircle L, ℂ) →L[ℂ] C(AddCircle L, ℂ) => B f) hAG

theorem periodicL2Heat_norm_le {τ t : ℝ} (hτ : 0 < τ) (ht : τ ≤ t)
    (u : Lp ℂ 2 (haarAddCircle (T := L))) :
    ‖periodicL2Heat t (lt_of_lt_of_le hτ ht) u‖ ≤
      ((1 + τ⁻¹) * ‖(⟨(fun n : ℤ =>
          1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
        memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖) * ‖u‖ := by
  let d : lp (fun _ : ℤ => ℝ) 2 :=
    ⟨fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2),
      memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩
  let w : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨fun n : ℤ => (Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * t) : ℂ),
      memℓp_periodicHeatWeight (lt_of_lt_of_le hτ ht)⟩
  have hw : ‖w‖ ≤ ‖(1 + τ⁻¹) • d‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro n
    change ‖(Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * t) : ℂ)‖ ≤
      ‖(1 + τ⁻¹) * (1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2))‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact periodicHeatWeight_bound hτ ht n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + τ⁻¹)] at hw
  change ‖weightedFourier w (fourierBasis.repr u)‖ ≤ ((1 + τ⁻¹) * ‖d‖) * ‖u‖
  exact (norm_weightedFourier_le w (fourierBasis.repr u)).trans
    (by simpa only [LinearIsometryEquiv.norm_map] using
      mul_le_mul_of_nonneg_right hw (norm_nonneg (fourierBasis.repr u)))

theorem tendsto_periodicGaussianHeat_of_tendsto_L2 {ι : Type*} {l : Filter ι}
    {times : ι → ℝ} {t : ℝ} (ht : 0 < t) (htimes : Tendsto times l (𝓝 t))
    {slices : ι → C(AddCircle L, ℂ)} {f : C(AddCircle L, ℂ)}
    (hslices : Tendsto (fun i => ContinuousMap.toLp 2 haarAddCircle ℂ (slices i)) l
      (𝓝 (ContinuousMap.toLp 2 haarAddCircle ℂ f))) :
    Tendsto (fun i => periodicGaussianHeat (times i) (slices i)) l
      (𝓝 (periodicGaussianHeat t f)) := by
  let C : ℝ := (1 + (t / 2)⁻¹) * ‖(⟨(fun n : ℤ =>
      1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  have htime : ∀ᶠ i in l, t / 2 ≤ times i :=
    htimes.eventually (eventually_ge_nhds (by linarith : t / 2 < t))
  have hd : Tendsto (fun i => ContinuousMap.toLp 2 haarAddCircle ℂ (slices i - f)) l
      (𝓝 0) := by
    simpa only [map_sub, sub_self] using hslices.sub
      (tendsto_const_nhds (x := ContinuousMap.toLp 2 haarAddCircle ℂ f))
  have hb : ∀ᶠ i in l, ‖periodicGaussianHeat (times i) (slices i - f)‖ ≤
      C * ‖ContinuousMap.toLp 2 haarAddCircle ℂ (slices i - f)‖ := by
    filter_upwards [htime] with i hi
    have hpos : 0 < times i := lt_of_lt_of_le (by linarith : 0 < t / 2) hi
    rw [← periodicL2Heat_eq_gaussian (times i) hpos]
    exact periodicL2Heat_norm_le (by linarith : 0 < t / 2) hi _
  have hn : Tendsto (fun i => ‖periodicGaussianHeat (times i) (slices i - f)‖) l
      (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) hb
      (by simpa only [norm_zero, mul_zero] using hd.norm.const_mul C)
  have hz : Tendsto (fun i => periodicGaussianHeat (times i) (slices i - f)) l
      (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hf := (periodicGaussianHeat_properties f).2.2.continuousAt.tendsto.comp htimes
  simpa only [map_sub, Function.comp_def, sub_add_cancel, zero_add] using hz.add hf

end PoincareConjecture.M63
