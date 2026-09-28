import PoincareConjecture.Proofs.M03.Existence.SpectralShiftedNative
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*}

def scaleWeight (lambda : iota → NNReal) (k : ℕ) (i : iota) : ℝ :=
  Real.sqrt (1 + (lambda i : ℝ)) ^ k

theorem one_le_scaleWeight (lambda : iota → NNReal) (k : ℕ) (i : iota) :
    1 ≤ scaleWeight lambda k i := by
  apply one_le_pow₀
  simpa only [Real.sqrt_one] using
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (lambda i).coe_nonneg :
      (1 : ℝ) ≤ 1 + (lambda i : ℝ))

theorem scaleWeight_pos (lambda : iota → NNReal) (k : ℕ) (i : iota) :
    0 < scaleWeight lambda k i := lt_of_lt_of_le zero_lt_one (one_le_scaleWeight lambda k i)

@[simp] theorem scaleWeight_zero (lambda : iota → NNReal) (i : iota) :
    scaleWeight lambda 0 i = 1 := pow_zero _

theorem scaleWeight_add (lambda : iota → NNReal) (k l : ℕ) (i : iota) :
    scaleWeight lambda (k + l) i = scaleWeight lambda k i * scaleWeight lambda l i :=
  pow_add _ _ _

theorem scaleWeight_two (lambda : iota → NNReal) (i : iota) :
    scaleWeight lambda 2 i = 1 + (lambda i : ℝ) :=
  Real.sq_sqrt (by positivity)

private theorem inverse_scaleWeight_bound (lambda : iota → NNReal) (k : ℕ) (i : iota) :
    |(scaleWeight lambda k i)⁻¹| ≤ 1 := by
  rw [abs_of_pos (inv_pos.mpr (scaleWeight_pos lambda k i)),
    inv_le_one₀ (scaleWeight_pos lambda k i)]
  exact one_le_scaleWeight lambda k i

def scaleDecode (lambda : iota → NNReal) (k : ℕ) : State iota →L[ℝ] State iota :=
  multiplier (fun i => (scaleWeight lambda k i)⁻¹) 1 zero_le_one
    (inverse_scaleWeight_bound lambda k)

@[simp] theorem scaleDecode_apply (lambda : iota → NNReal) (k : ℕ)
    (z : State iota) (i : iota) :
    scaleDecode lambda k z i = (scaleWeight lambda k i)⁻¹ * z i := rfl

theorem norm_scaleDecode_le (lambda : iota → NNReal) (k : ℕ) (z : State iota) :
    ‖scaleDecode lambda k z‖ ≤ ‖z‖ := by
  simpa only [scaleDecode, one_mul] using
    norm_multiplier_apply_le _ 1 zero_le_one (inverse_scaleWeight_bound lambda k) z

theorem scaleDecode_injective (lambda : iota → NNReal) (k : ℕ) :
    Function.Injective (scaleDecode lambda k) := by
  intro z w h
  apply lp.ext
  funext i
  exact mul_left_cancel₀ (inv_ne_zero (scaleWeight_pos lambda k i).ne')
    (congrArg (fun x : State iota => x i) h)

@[simp] theorem scaleDecode_zero (lambda : iota → NNReal) :
    scaleDecode lambda 0 = ContinuousLinearMap.id ℝ (State iota) := by
  ext z i
  simp

theorem scaleDecode_add (lambda : iota → NNReal) (k l : ℕ) :
    scaleDecode lambda (k + l) = (scaleDecode lambda k).comp (scaleDecode lambda l) := by
  ext z i
  simp only [scaleDecode_apply, scaleWeight_add, mul_inv_rev, ContinuousLinearMap.comp_apply]
  ring

def InScale (lambda : iota → NNReal) (k : ℕ) (u : State iota) : Prop :=
  Memℓp (fun i => scaleWeight lambda k i * u i) 2

def scaleEncode (lambda : iota → NNReal) (k : ℕ) (u : State iota)
    (hu : InScale lambda k u) : State iota :=
  ⟨fun i => scaleWeight lambda k i * u i, hu⟩

@[simp] theorem scaleEncode_apply (lambda : iota → NNReal) (k : ℕ) (u : State iota)
    (hu : InScale lambda k u) (i : iota) :
    scaleEncode lambda k u hu i = scaleWeight lambda k i * u i := rfl

theorem scaleDecode_scaleEncode (lambda : iota → NNReal) (k : ℕ) (u : State iota)
    (hu : InScale lambda k u) : scaleDecode lambda k (scaleEncode lambda k u hu) = u := by
  apply lp.ext
  funext i
  simp only [scaleDecode_apply, scaleEncode_apply, ← mul_assoc,
    inv_mul_cancel₀ (scaleWeight_pos lambda k i).ne', one_mul]

theorem inScale_scaleDecode (lambda : iota → NNReal) (k : ℕ) (z : State iota) :
    InScale lambda k (scaleDecode lambda k z) := by
  have heq : (fun i => scaleWeight lambda k i * scaleDecode lambda k z i) = z := by
    funext i
    simp only [scaleDecode_apply, ← mul_assoc,
      mul_inv_cancel₀ (scaleWeight_pos lambda k i).ne', one_mul]
  unfold InScale
  rw [heq]
  exact lp.memℓp z

theorem scaleEncode_scaleDecode (lambda : iota → NNReal) (k : ℕ) (z : State iota) :
    scaleEncode lambda k (scaleDecode lambda k z) (inScale_scaleDecode lambda k z) = z := by
  apply scaleDecode_injective lambda k
  exact scaleDecode_scaleEncode lambda k _ _

theorem inScale_iff_mem_range (lambda : iota → NNReal) (k : ℕ) (u : State iota) :
    InScale lambda k u ↔ u ∈ Set.range (scaleDecode lambda k) := by
  constructor
  · intro hu
    exact ⟨scaleEncode lambda k u hu, scaleDecode_scaleEncode lambda k u hu⟩
  · rintro ⟨z, rfl⟩
    exact inScale_scaleDecode lambda k z

theorem norm_scaleEncode_sq (lambda : iota → NNReal) (k : ℕ) (u : State iota)
    (hu : InScale lambda k u) :
    ‖scaleEncode lambda k u hu‖ ^ 2 =
      ∑' i, scaleWeight lambda k i ^ 2 * u i ^ 2 := by
  rw [norm_sq_eq_tsum]
  apply tsum_congr
  intro i
  simp only [scaleEncode_apply, sq_abs, mul_pow]

theorem scaleDecode_single [DecidableEq iota]
    (lambda : iota → NNReal) (k : ℕ) (i : iota) (a : ℝ) :
    scaleDecode lambda k (lp.single 2 i (scaleWeight lambda k i * a)) = lp.single 2 i a := by
  classical
  apply lp.ext
  funext j
  by_cases h : j = i
  · subst j
    simp only [scaleDecode_apply, lp.single_apply_self, ← mul_assoc,
      inv_mul_cancel₀ (scaleWeight_pos lambda k i).ne', one_mul]
  · simp only [scaleDecode_apply, lp.single_apply_ne _ _ _ h, mul_zero]

theorem scaleDecode_denseRange (lambda : iota → NNReal) (k : ℕ) :
    DenseRange (scaleDecode lambda k) := by
  classical
  intro u
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u)
  apply Eventually.of_forall
  intro s
  refine ⟨∑ i ∈ s, lp.single 2 i (scaleWeight lambda k i * u i), ?_⟩
  simp only [map_sum, scaleDecode_single]

theorem scaleDecode_heat (lambda : iota → NNReal) (k : ℕ) (t : NNReal) (z : State iota) :
    scaleDecode lambda k (heat lambda t z) = heat lambda t (scaleDecode lambda k z) := by
  apply lp.ext
  funext i
  simp only [scaleDecode_apply, heat_apply]
  ring

theorem scaleDecode_responseState [Countable iota] {T t : ℝ}
    (lambda : iota → NNReal) (k : ℕ) {F : ℝ → State iota}
    (hF : MemLp F 2 (timeMeasure T)) (ht : t ∈ Icc (0 : ℝ) T) :
    scaleDecode lambda k (responseState lambda F t) =
      responseState lambda (fun s => scaleDecode lambda k (F s)) t := by
  have hdec : MemLp (fun s => scaleDecode lambda k (F s)) 2 (timeMeasure T) :=
    (scaleDecode lambda k).comp_memLp' hF
  apply lp.ext
  funext i
  rw [scaleDecode_apply, responseState_apply_of_memLp hF lambda ht,
    responseState_apply_of_memLp hdec lambda ht]
  change (scaleWeight lambda k i)⁻¹ * spectralMode (lambda i) 0 (fun s => F s i) t =
    spectralMode (lambda i) 0 (fun s => (scaleWeight lambda k i)⁻¹ * F s i) t
  simp only [spectralMode, zero_add]
  have heq : (fun s : ℝ => Real.exp ((lambda i : ℝ) * s) *
      ((scaleWeight lambda k i)⁻¹ * F s i)) =
      (fun s => (scaleWeight lambda k i)⁻¹ * (Real.exp ((lambda i : ℝ) * s) * F s i)) := by
    funext s
    ring
  rw [heq, intervalIntegral.integral_const_mul]
  ring

theorem scaleDecode_shiftedTracePath [Countable iota] {T : ℝ}
    (hT : 0 ≤ T) (lambda : iota → NNReal) (F : ForcingSpace iota T)
    (t : Icc (0 : ℝ) T) :
    scaleDecode lambda 1 (shiftedTracePath hT lambda F t) = responseState lambda F t := by
  apply lp.ext
  funext i
  rw [scaleDecode_apply, shiftedTracePath_coeff]
  change (Real.sqrt (1 + (lambda i : ℝ)) ^ 1)⁻¹ *
    (Real.sqrt (1 + (lambda i : ℝ)) * responseState lambda F t i) = _
  rw [pow_one, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem inScale_one_response [Countable iota] {T : ℝ}
    (hT : 0 ≤ T) (lambda : iota → NNReal) (F : ForcingSpace iota T)
    (t : Icc (0 : ℝ) T) : InScale lambda 1 (responseState lambda F t) := by
  rw [← scaleDecode_shiftedTracePath hT lambda F t]
  exact inScale_scaleDecode lambda 1 _

theorem scaleDecode_shiftedHigh [Countable iota] {T : ℝ}
    (hT : 0 ≤ T) (lambda : iota → NNReal) (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T,
      scaleDecode lambda 2 (shiftedHighOperator hT lambda F t) = responseState lambda F t := by
  filter_upwards [shiftedHighOperator_coeff hT lambda F] with t ht
  apply lp.ext
  funext i
  rw [scaleDecode_apply, scaleWeight_two, ht i, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

theorem ae_inScale_two_response [Countable iota] {T : ℝ}
    (hT : 0 ≤ T) (lambda : iota → NNReal) (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T, InScale lambda 2 (responseState lambda F t) := by
  filter_upwards [scaleDecode_shiftedHigh hT lambda F] with t ht
  rw [← ht]
  exact inScale_scaleDecode lambda 2 _

theorem scaleWeight_sq (lambda : iota → NNReal) (k : ℕ) (i : iota) :
    scaleWeight lambda k i ^ 2 = (1 + (lambda i : ℝ)) ^ k := by
  unfold scaleWeight
  rw [pow_right_comm, Real.sq_sqrt (by positivity)]

theorem inScale_iff_summable_weighted_sq (lambda : iota → NNReal)
    (k : ℕ) (u : State iota) :
    InScale lambda k u ↔ Summable (fun i => (1 + (lambda i : ℝ)) ^ k * u i ^ 2) := by
  unfold InScale
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
    sq_abs, mul_pow, scaleWeight_sq]

theorem norm_scaleEncode_sq_eq_mass (lambda : iota → NNReal) (k : ℕ)
    (u : State iota) (hu : InScale lambda k u) :
    ‖scaleEncode lambda k u hu‖ ^ 2 =
      ∑' i, (1 + (lambda i : ℝ)) ^ k * u i ^ 2 := by
  rw [norm_scaleEncode_sq]
  simp only [scaleWeight_sq]

theorem inScale_mono (lambda : iota → NNReal) {k l : ℕ} (hkl : k ≤ l)
    {u : State iota} (hu : InScale lambda l u) : InScale lambda k u := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [inScale_iff_mem_range]
  refine ⟨scaleDecode lambda j (scaleEncode lambda (k + j) u hu), ?_⟩
  rw [← ContinuousLinearMap.comp_apply, ← scaleDecode_add, scaleDecode_scaleEncode]

theorem inScale_sub (lambda : iota → NNReal) (k : ℕ) {u v : State iota}
    (hu : InScale lambda k u) (hv : InScale lambda k v) : InScale lambda k (u - v) := by
  change Memℓp (fun i => scaleWeight lambda k i * (u i - v i)) 2
  have heq : (fun i => scaleWeight lambda k i * (u i - v i)) =
      ((fun i => scaleWeight lambda k i * u i) - fun i => scaleWeight lambda k i * v i) := by
    funext i
    exact mul_sub _ _ _
  rw [heq]
  exact hu.sub hv

theorem scaleEncode_sub (lambda : iota → NNReal) (k : ℕ) (u v : State iota)
    (hu : InScale lambda k u) (hv : InScale lambda k v) :
    scaleEncode lambda k (u - v) (inScale_sub lambda k hu hv) =
      scaleEncode lambda k u hu - scaleEncode lambda k v hv := by
  apply lp.ext
  funext i
  simp only [scaleEncode_apply, lp.coeFn_sub, Pi.sub_apply, mul_sub]

theorem norm_scaleEncode_sq_eq_inner (lambda : iota → NNReal) (k : ℕ)
    (u : State iota) (hu : InScale lambda (2 * k) u) :
    ‖scaleEncode lambda k u (inScale_mono lambda (by omega) hu)‖ ^ 2 =
      inner ℝ u (scaleEncode lambda (2 * k) u hu) := by
  rw [norm_scaleEncode_sq, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [Real.inner_apply, scaleEncode_apply, show 2 * k = k + k by omega,
    scaleWeight_add]
  ring

theorem norm_scaleEncode_sq_le (lambda : iota → NNReal) (k : ℕ)
    (u : State iota) (hu : InScale lambda (2 * k) u) :
    ‖scaleEncode lambda k u (inScale_mono lambda (by omega) hu)‖ ^ 2 ≤
      ‖u‖ * ‖scaleEncode lambda (2 * k) u hu‖ := by
  rw [norm_scaleEncode_sq_eq_inner]
  exact real_inner_le_norm _ _

theorem continuous_scaleEncode_of_double_bound {X : Type*} [TopologicalSpace X]
    (lambda : iota → NNReal) (k : ℕ) (U : X → State iota) (hU : Continuous U)
    (hscale : ∀ t, InScale lambda (2 * k) (U t)) {B : ℝ}
    (hbound : ∀ t, ‖scaleEncode lambda (2 * k) (U t) (hscale t)‖ ≤ B) :
    Continuous (fun t => scaleEncode lambda k (U t)
      (inScale_mono lambda (by omega) (hscale t))) := by
  let Z : X → State iota := fun t => scaleEncode lambda k (U t)
    (inScale_mono lambda (by omega) (hscale t))
  have hdiff (s t : X) : ‖Z s - Z t‖ ^ 2 ≤ ‖U s - U t‖ * (2 * B) := by
    have hs := inScale_mono lambda (show k ≤ 2 * k by omega) (hscale s)
    have ht := inScale_mono lambda (show k ≤ 2 * k by omega) (hscale t)
    have hsub := inScale_sub lambda (2 * k) (hscale s) (hscale t)
    calc
      _ = ‖scaleEncode lambda k (U s - U t)
          (inScale_mono lambda (by omega) hsub)‖ ^ 2 := by
        rw [scaleEncode_sub lambda k (U s) (U t) hs ht]
      _ ≤ ‖U s - U t‖ * ‖scaleEncode lambda (2 * k) (U s - U t) hsub‖ :=
        norm_scaleEncode_sq_le lambda k (U s - U t) hsub
      _ = ‖U s - U t‖ * ‖scaleEncode lambda (2 * k) (U s) (hscale s) -
          scaleEncode lambda (2 * k) (U t) (hscale t)‖ := by rw [scaleEncode_sub]
      _ ≤ ‖U s - U t‖ * (2 * B) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [hbound s, hbound t])
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbase : Tendsto (fun s => ‖U s - U t‖ * (2 * B)) (𝓝 t) (𝓝 0) := by
    have h := ((hU.continuousAt (x := t)).tendsto.sub_const (U t)).norm.mul_const (2 * B)
    simpa only [sub_self, norm_zero, zero_mul] using h
  have hsq : Tendsto (fun s => ‖Z s - Z t‖ ^ 2) (𝓝 t) (𝓝 0) :=
    squeeze_zero (fun s => sq_nonneg _) (fun s => hdiff s t) hbase
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

theorem exists_continuous_scale_lift_of_mass {X : Type*} [TopologicalSpace X]
    (lambda : iota → NNReal) (k : ℕ) (U : X → State iota) (hU : Continuous U)
    {B : ℝ} (hB : 0 ≤ B)
    (hmass : ∀ t, Summable (fun i => (1 + (lambda i : ℝ)) ^ (2 * k) * U t i ^ 2) ∧
      (∑' i, (1 + (lambda i : ℝ)) ^ (2 * k) * U t i ^ 2) ≤ B) :
    ∃ Z : C(X, State iota), (∀ t, scaleDecode lambda k (Z t) = U t) ∧
      (∀ t i, Z t i = scaleWeight lambda k i * U t i) := by
  have hs (t : X) : InScale lambda (2 * k) (U t) :=
    (inScale_iff_summable_weighted_sq lambda (2 * k) (U t)).mpr (hmass t).1
  have hb (t : X) : ‖scaleEncode lambda (2 * k) (U t) (hs t)‖ ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hB, norm_scaleEncode_sq_eq_mass]
    exact (hmass t).2
  refine ⟨⟨fun t => scaleEncode lambda k (U t) (inScale_mono lambda (by omega) (hs t)),
    continuous_scaleEncode_of_double_bound lambda k U hU hs hb⟩, ?_, ?_⟩
  · intro t
    exact scaleDecode_scaleEncode lambda k (U t) _
  · intro t i
    rfl

theorem hasDerivWithinAt_responseState_of_scale_path [Countable iota] {T : ℝ}
    (hT : 0 ≤ T) (lambda : iota → NNReal) (F : ForcingSpace iota T)
    {f : ℝ → State iota} (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hF : F =ᵐ[timeMeasure T] f) (Z : C(Icc (0 : ℝ) T, State iota))
    (hZ : ∀ t : Icc (0 : ℝ) T,
      scaleDecode lambda 2 (Z t) = responseState lambda F t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (responseState lambda F)
      (f t - (Z ⟨t, ht⟩ - responseState lambda F t)) (Icc (0 : ℝ) T) t := by
  let Zext : ℝ → State iota := IccExtend hT (Z : Icc (0 : ℝ) T → State iota)
  let H : ℝ → State iota := fun s => f s - (Zext s - responseState lambda F s)
  have hZext : Continuous Zext := Z.continuous.Icc_extend'
  have hH : ContinuousOn H (Icc (0 : ℝ) T) :=
    hf.sub (hZext.continuousOn.sub (continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda))
  have hZcoeff (s : Icc (0 : ℝ) T) (i : iota) :
      Z s i = (1 + (lambda i : ℝ)) * responseState lambda F s i := by
    have h := congrArg (fun u : State iota => (1 + (lambda i : ℝ)) * u i) (hZ s)
    simpa only [scaleDecode_apply, scaleWeight_two, ← mul_assoc,
      mul_inv_cancel₀ (by positivity : (1 + (lambda i : ℝ)) ≠ 0), one_mul] using h
  have hgenerator : generatorState lambda F =ᵐ[timeMeasure T]
      (fun s => Zext s - responseState lambda F s) := by
    filter_upwards [ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda,
      ae_restrict_mem measurableSet_Ioc] with s hs hmem
    apply lp.ext
    funext i
    have hsi := Ioc_subset_Icc_self hmem
    change generatorState lambda F s i = Zext s i - responseState lambda F s i
    rw [hs i, show Zext s = Z ⟨s, hsi⟩ from IccExtend_of_mem hT _ hsi, hZcoeff]
    ring
  have hderivative : derivativeState lambda F =ᵐ[timeMeasure T] H := by
    filter_upwards [derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda,
      hgenerator, hF] with s hs hgen hforce
    rw [hgen, hforce] at hs
    exact eq_sub_of_add_eq hs
  have hresponse : ∀ s ∈ Icc (0 : ℝ) T,
      responseState lambda F s = volterraPath (0 : State iota) H s := by
    intro s hs
    simp only [responseState, volterraPath, zero_add]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hs.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl hs.2) hderivative] with s hs
    exact hs
  have hd := (hasDerivWithinAt_volterraPath_Icc (x₀ := (0 : State iota)) hH ht).congr_of_mem
    hresponse ht
  simpa only [H, Zext, IccExtend_of_mem hT _ ht] using hd

theorem hasDerivWithinAt_responseState_right_of_scale_path [Countable iota] {T : ℝ}
    (hT : 0 ≤ T) (lambda : iota → NNReal) (F : ForcingSpace iota T)
    {f : ℝ → State iota} (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hF : F =ᵐ[timeMeasure T] f) (Z : C(Icc (0 : ℝ) T, State iota))
    (hZ : ∀ t : Icc (0 : ℝ) T,
      scaleDecode lambda 2 (Z t) = responseState lambda F t)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (responseState lambda F)
      (f t - (Z ⟨t, Ico_subset_Icc_self ht⟩ - responseState lambda F t)) (Ici t) t :=
  (hasDerivWithinAt_responseState_of_scale_path hT lambda F hf hF Z hZ
    (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

end PoincareConjecture.SpectralHeatNative
