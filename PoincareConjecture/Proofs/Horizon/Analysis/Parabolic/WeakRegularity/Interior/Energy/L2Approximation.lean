import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.RescaledApproximation
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.L2Space

open Set Filter MeasureTheory ContinuousLinearMap
open Poincare.Analysis.Convolution
open scoped ContDiff Topology Convolution ENNReal

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

local instance {n : ℕ} : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem tendsto_rescaledKernel_lp_average
    {n : ℕ} (u : Lp ℝ 2 (volume : Measure (Spacetime n)))
    {ρ : Spacetime n → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hmass : (∫ y, ρ y) = 1) {r : ℕ → ℝ} (hr : ∀ m, 0 < r m)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun m => ∫ y : Spacetime n,
      rescaledKernel ρ (r m) y • (DomAddAct.mk (-y) +ᵥ u)) atTop (𝓝 u) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : ContinuousVAdd (Spacetime n)ᵈᵃᵃ
      (Lp ℝ 2 (volume : Measure (Spacetime n))) :=
    MeasureTheory.Lp.instContinuousVAddDomAddAct
  let T : Spacetime n → Lp ℝ 2 (volume : Measure (Spacetime n)) :=
    fun y => DomAddAct.mk y +ᵥ u
  have hT : Continuous T := DomAddAct.continuous_mk.vadd continuous_const
  let M : ℝ := ∫ y, ‖ρ y‖
  have hM : 0 ≤ M := integral_nonneg (fun y => norm_nonneg _)
  obtain ⟨R, hRpos, hR⟩ := hρc.isBounded.exists_pos_norm_lt
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hmodpos : 0 < ε / (2 * (M + 1)) := by positivity
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.continuousAt_iff.mp hT.continuousAt (ε / (2 * (M + 1))) hmodpos
  filter_upwards [hlim.eventually_lt_const (div_pos hδ hRpos)] with m hm
  have hscale : ContDiff ℝ ∞ (rescaledKernel ρ (r m)) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul (r m)⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ (r m)) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 (r m)⁻¹ (inv_ne_zero (hr m).ne')))).mul_left
  have hsupport : Function.support (rescaledKernel ρ (r m)) ⊆
      Metric.ball (0 : Spacetime n) (r m * R) := by
    intro y hy
    have hρy : ρ ((r m)⁻¹ • y) ≠ 0 := by
      intro he
      exact hy (by simp [rescaledKernel, he])
    have hb := hR _ (subset_tsupport ρ hρy)
    have hn : ‖(r m)⁻¹ • y‖ = (r m)⁻¹ * ‖y‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos (hr m)]
    rw [hn] at hb
    have hb' := mul_lt_mul_of_pos_left hb (hr m)
    simpa [mem_ball_zero_iff, ← mul_assoc, (hr m).ne'] using hb'
  have habs : (∫ y, ‖rescaledKernel ρ (r m) y‖) = M := by
    have he : (fun y => ‖rescaledKernel ρ (r m) y‖) =
        rescaledKernel (fun y => ‖ρ y‖) (r m) := by
      funext y
      simp only [rescaledKernel, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow,
        abs_of_pos (hr m)]
    rw [he, integral_rescaledKernel volume _ (hr m)]
  have hd := dist_convolution_le' (μ := volume) (lsmul ℝ ℝ) hmodpos.le
    (hscale.continuous.integrable_of_hasCompactSupport hcompact) hsupport
    hT.aestronglyMeasurable (x₀ := 0) (z₀ := u)
    (fun y hy => by
      have he := (hmod ((Metric.mem_ball.mp hy).trans
        ((lt_div_iff₀ hRpos).mp hm))).le
      simpa [T] using he)
  simp only [lsmul_apply, integral_smul_const,
    integral_rescaledKernel volume ρ (hr m), hmass, one_smul, habs] at hd
  have hb : (‖(lsmul ℝ ℝ : ℝ →L[ℝ]
      (Lp ℝ 2 (volume : Measure (Spacetime n))) →L[ℝ]
      (Lp ℝ 2 (volume : Measure (Spacetime n))))‖ * M) *
      (ε / (2 * (M + 1))) ≤ M * (ε / (2 * (M + 1))) := by
    apply mul_le_mul_of_nonneg_right _ hmodpos.le
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (opNorm_lsmul_le (𝕜 := ℝ) (R := ℝ)
        (E := Lp ℝ 2 (volume : Measure (Spacetime n)))) hM
  have hsmall : M * (ε / (2 * (M + 1))) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * (M + 1))]
    nlinarith
  simpa only [convolution, lsmul_apply, zero_sub, T] using
    hd.trans_lt (hb.trans_lt hsmall)

private theorem integrable_kernel_test_translate
    {n : ℕ} (u : Lp ℝ 2 (volume : Measure (Spacetime n)))
    {η φ : Spacetime n → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : Spacetime n × Spacetime n =>
      η p.1 * (φ p.2 * u (p.2 - p.1))) (volume.prod volume) := by
  have hφ2 : MemLp φ 2 volume := hφ.memLp_of_hasCompactSupport hφc
  have hut (y : Spacetime n) : MemLp (fun x => u (x - y)) 2 volume := by
    exact (Lp.memLp u).comp_measurePreserving (measurePreserving_sub_right volume y)
  have hsec (y : Spacetime n) : Integrable (fun x => φ x * u (x - y)) volume :=
    hφ2.integrable_mul (hut y)
  have hmeas : StronglyMeasurable (fun p : Spacetime n × Spacetime n =>
      η p.1 * (φ p.2 * u (p.2 - p.1))) :=
    (hη.stronglyMeasurable.comp_measurable measurable_fst).mul
      ((hφ.stronglyMeasurable.comp_measurable measurable_snd).mul
        ((Lp.stronglyMeasurable u).comp_measurable (measurable_snd.sub measurable_fst)))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Eventually.of_forall (fun y => (hsec y).const_mul (η y)), ?_⟩
  let C : ℝ := ((∫ x, φ x ^ 2) + ∫ x, (u x) ^ 2) / 2
  have hbound (y : Spacetime n) : (∫ x, ‖φ x * u (x - y)‖) ≤ C := by
    have hi := integral_mono (hsec y).norm
      ((hφ2.integrable_sq.add (hut y).integrable_sq).div_const 2)
      (fun x => by
        simp only [Pi.add_apply]
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        nlinarith [sq_nonneg (|φ x| - |u (x-y)|), sq_abs (φ x), sq_abs (u (x-y))])
    have he : (∫ x, (u (x-y)) ^ 2) = ∫ x, (u x) ^ 2 :=
      integral_sub_right_eq_self (fun x => (u x) ^ 2) y
    simpa only [Pi.add_apply, integral_div, integral_add hφ2.integrable_sq (hut y).integrable_sq,
      he, C] using hi
  apply ((hη.integrable_of_hasCompactSupport hηc).norm.mul_const C).mono'
    hmeas.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  simp only [norm_mul, integral_const_mul]
  simpa only [norm_mul] using mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg (η y))

theorem lp_average_ae_eq_lebesgueConvolution
    {n : ℕ} (u : Lp ℝ 2 (volume : Measure (Spacetime n)))
    {η : Spacetime n → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η) :
    ((∫ y : Spacetime n, η y • (DomAddAct.mk (-y) +ᵥ u)) :
      Lp ℝ 2 (volume : Measure (Spacetime n))) =ᵐ[volume]
      lebesgueConvolution η u := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : ContinuousVAdd (Spacetime n)ᵈᵃᵃ
      (Lp ℝ 2 (volume : Measure (Spacetime n))) :=
    MeasureTheory.Lp.instContinuousVAddDomAddAct
  let T : Spacetime n → Lp ℝ 2 (volume : Measure (Spacetime n)) :=
    fun y => η y • (DomAddAct.mk (-y) +ᵥ u)
  have hT : Continuous T := hη.smul
    ((DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const)
  have hTc : HasCompactSupport T := hηc.smul_right
  have hTi : Integrable T volume := hT.integrable_of_hasCompactSupport hTc
  have hconv : Continuous (lebesgueConvolution η u) := by
    rw [lebesgueConvolution_eq_convolution]
    exact hηc.continuous_convolution_left (lsmul ℝ ℝ) hη
      ((Lp.memLp u).locallyIntegrable (by norm_num))
  apply ae_eq_of_integral_contDiff_smul_eq
    (Lp.memLp _ |>.locallyIntegrable (by norm_num)) hconv.locallyIntegrable
  intro φ hφ hφc
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
  let v : Lp ℝ 2 (volume : Measure (Spacetime n)) := hφ2.toLp φ
  have hv : v =ᵐ[volume] φ := hφ2.coeFn_toLp
  have hinner (w : Lp ℝ 2 (volume : Measure (Spacetime n))) :
      inner ℝ v w = ∫ x, φ x * w x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx, mul_comm]
  calc
    (∫ x, φ x • (∫ y, T y) x) = inner ℝ v (∫ y, T y) := by
      rw [hinner]
      rfl
    _ = ∫ y, inner ℝ v (T y) := (integral_inner (𝕜 := ℝ) hTi v).symm
    _ = ∫ y, ∫ x, η y * (φ x * u (x-y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hinner]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul (η y) (DomAddAct.mk (-y) +ᵥ u),
        DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) u] with x hx ht
      change φ x * (η y • (DomAddAct.mk (-y) +ᵥ u)) x = _
      rw [hx]
      change φ x * (η y * (DomAddAct.mk (-y) +ᵥ u) x) = _
      rw [ht]
      simp [sub_eq_add_neg, add_comm, mul_left_comm]
    _ = ∫ x, ∫ y, η y * (φ x * u (x-y)) :=
      integral_integral_swap (integrable_kernel_test_translate u
        hη hηc hφ.continuous hφc)
    _ = ∫ x, φ x • lebesgueConvolution η u x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [lebesgueConvolution_eq_convolution]
      simp only [convolution, lsmul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring

private theorem lp_average_toLp_ae_eq_lebesgueConvolution
    {n : ℕ} {u η : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    ((∫ y : Spacetime n, η y • (DomAddAct.mk (-y) +ᵥ hu.toLp u)) :
      Lp ℝ 2 (volume : Measure (Spacetime n))) =ᵐ[volume]
      lebesgueConvolution η u := by
  refine (lp_average_ae_eq_lebesgueConvolution (hu.toLp u) hη hηc).trans ?_
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with y hy
  rw [hy]

theorem memLp_lebesgueConvolution
    {n : ℕ} {u η : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    MemLp (lebesgueConvolution η u) 2 volume :=
  MemLp.ae_eq (lp_average_toLp_ae_eq_lebesgueConvolution hu hη hηc) (Lp.memLp _)

theorem norm_toLp_lebesgueConvolution_le
    {n : ℕ} {u η : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    ‖(memLp_lebesgueConvolution hu hη hηc).toLp (lebesgueConvolution η u)‖ ≤
      (∫ y, ‖η y‖) * ‖hu.toLp u‖ := by
  have he : (memLp_lebesgueConvolution hu hη hηc).toLp (lebesgueConvolution η u) =
      ∫ y : Spacetime n, η y • (DomAddAct.mk (-y) +ᵥ hu.toLp u) :=
    Lp.ext ((memLp_lebesgueConvolution hu hη hηc).coeFn_toLp.trans
      (lp_average_toLp_ae_eq_lebesgueConvolution hu hη hηc).symm)
  rw [he]
  simpa only [norm_smul, DomAddAct.norm_vadd_Lp, integral_mul_const] using
    norm_integral_le_integral_norm
      (fun y : Spacetime n => η y • (DomAddAct.mk (-y) +ᵥ hu.toLp u))

theorem tendsto_mollifiedValue_toLp
    {n : ℕ} {u ρ : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hmass : (∫ y, ρ y) = 1) {r : ℕ → ℝ} (hr : ∀ m, 0 < r m)
    (hlim : Tendsto r atTop (𝓝 0)) :
    ∃ hm : ∀ m, MemLp (mollifiedValue u ρ (r m)) 2 volume,
      Tendsto (fun m => (hm m).toLp (mollifiedValue u ρ (r m))) atTop
        (𝓝 (hu.toLp u)) := by
  let A (m : ℕ) : Lp ℝ 2 (volume : Measure (Spacetime n)) :=
    ∫ y, rescaledKernel ρ (r m) y • (DomAddAct.mk (-y) +ᵥ hu.toLp u)
  have he (m : ℕ) : A m =ᵐ[volume] mollifiedValue u ρ (r m) := by
    have hscale : ContDiff ℝ ∞ (rescaledKernel ρ (r m)) :=
      contDiff_const.mul (hρ.comp (contDiff_id.const_smul (r m)⁻¹))
    have hcompact : HasCompactSupport (rescaledKernel ρ (r m)) :=
      (hρc.comp_homeomorph
        (Homeomorph.smul (Units.mk0 (r m)⁻¹ (inv_ne_zero (hr m).ne')))).mul_left
    exact lp_average_toLp_ae_eq_lebesgueConvolution hu hscale.continuous hcompact
  have hm (m : ℕ) : MemLp (mollifiedValue u ρ (r m)) 2 volume :=
    MemLp.ae_eq (he m) (Lp.memLp (A m))
  refine ⟨hm, ?_⟩
  have hrep (m : ℕ) : (hm m).toLp (mollifiedValue u ρ (r m)) = A m :=
    Lp.ext ((hm m).coeFn_toLp.trans (he m).symm)
  simpa only [hrep] using
    tendsto_rescaledKernel_lp_average (hu.toLp u) hρ hρc hmass hr hlim

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
