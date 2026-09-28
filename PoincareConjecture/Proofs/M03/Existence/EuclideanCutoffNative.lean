import PoincareConjecture.Proofs.M03.Existence.EuclideanFirstOrderClosedNative
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct










set_option autoImplicit false

open MeasureTheory Set Filter LineDeriv
open scoped Topology ENNReal SchwartzMap LineDeriv ContDiff

noncomputable section

namespace PoincareConjecture.EuclideanDerivativeNative

section ZeroExtension

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
  {U : Set X} (hU : MeasurableSet U)

def zeroExtendL2Fun (f : Lp E 2 (μ.restrict U)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hU).mpr (Lp.memLp f)).toLp (U.indicator f)

theorem zeroExtendL2Fun_coe (f : Lp E 2 (μ.restrict U)) :
    zeroExtendL2Fun hU f =ᵐ[μ] U.indicator f := MemLp.coeFn_toLp _


def zeroExtendL2 : Lp E 2 (μ.restrict U) →ₗᵢ[ℝ] Lp E 2 μ where
  toFun := zeroExtendL2Fun hU
  map_add' f g := by
    apply Lp.ext
    have hmap := (ae_eq_restrict_iff_indicator_ae_eq hU).mp (Lp.coeFn_add f g)
    filter_upwards [zeroExtendL2Fun_coe hU (f + g), zeroExtendL2Fun_coe hU f,
      zeroExtendL2Fun_coe hU g, Lp.coeFn_add (zeroExtendL2Fun hU f) (zeroExtendL2Fun hU g),
      hmap] with x hsum hf hg hadd hxmap
    change zeroExtendL2Fun hU (f + g) x =
      (zeroExtendL2Fun hU f + zeroExtendL2Fun hU g) x
    rw [hsum, hadd, Pi.add_apply, hf, hg]
    by_cases hx : x ∈ U
    · simpa [hx] using hxmap
    · simp [hx]
  map_smul' a f := by
    apply Lp.ext
    have hmap := (ae_eq_restrict_iff_indicator_ae_eq hU).mp (Lp.coeFn_smul a f)
    filter_upwards [zeroExtendL2Fun_coe hU (a • f), zeroExtendL2Fun_coe hU f,
      Lp.coeFn_smul a (zeroExtendL2Fun hU f), hmap] with x hsmul hf ha hxmap
    change zeroExtendL2Fun hU (a • f) x = (a • zeroExtendL2Fun hU f) x
    rw [hsmul, ha, Pi.smul_apply, hf]
    by_cases hx : x ∈ U
    · simpa [hx] using hxmap
    · simp [hx]
  norm_map' f := by
    change ‖((memLp_indicator_iff_restrict hU).mpr (Lp.memLp f)).toLp
      (U.indicator f)‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hU, Lp.norm_def]

theorem zeroExtendL2_coe (f : Lp E 2 (μ.restrict U)) :
    zeroExtendL2 hU f =ᵐ[μ] U.indicator f := zeroExtendL2Fun_coe hU f

end ZeroExtension

variable {n : ℕ}

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

theorem contDiff_cutoff_mul (η : 𝓢(ModelE, ℝ)) {U : Set ModelE}
    (hU : IsOpen U) (hηU : tsupport η ⊆ U) {f : ModelE → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (fun x => η x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport η
  · exact (η.contDiffAt ⊤).mul (hf.contDiffAt (hU.mem_nhds (hηU hx)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]


def cutoffSchwartz (η : 𝓢(ModelE, ℝ)) (hη : HasCompactSupport η) {U : Set ModelE}
    (hU : IsOpen U) (hηU : tsupport η ⊆ U) (f : ModelE → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) : 𝓢(ModelE, ℝ) :=
  (hη.mul_right (f' := f)).toSchwartzMap (contDiff_cutoff_mul η hU hηU hf)

@[simp] theorem cutoffSchwartz_apply (η : 𝓢(ModelE, ℝ)) (hη : HasCompactSupport η)
    {U : Set ModelE} (hU : IsOpen U) (hηU : tsupport η ⊆ U) (f : ModelE → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (x : ModelE) :
    cutoffSchwartz η hη hU hηU f hf x = η x * f x := rfl


theorem fderiv_cutoff_mul (η : 𝓢(ModelE, ℝ)) {U : Set ModelE}
    (hU : IsOpen U) (hηU : tsupport η ⊆ U) {f : ModelE → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (x v : ModelE) :
    fderiv ℝ (fun y => η y * f y) x v =
      η x * fderiv ℝ f x v + f x * fderiv ℝ η x v := by
  by_cases hx : x ∈ tsupport η
  · rw [fderiv_fun_mul η.differentiableAt
      ((hf.contDiffAt (hU.mem_nhds (hηU hx))).differentiableAt (by simp))]
    rfl
  · have hzero : (η : ModelE → ℝ) =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hx
    have hprod : (fun y => η y * f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hzero] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    rw [hprod.fderiv_eq, hzero.fderiv_eq, hzero.eq_of_nhds]
    simp

theorem firstOrderSchwartz_apply {iota : Type*} [Fintype iota]
    (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE) (f : 𝓢(ModelE, ℝ)) (x : ModelE) :
    firstOrderSchwartz a v f x = ∑ i, a i x * fderiv ℝ f x (v i) := by
  simp only [firstOrderSchwartz, sum_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.pairing_apply_apply,
    LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    ContinuousLinearMap.mul_apply']

theorem tsupport_firstOrderSchwartz_subset {iota : Type*} [Fintype iota]
    (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE) (f : 𝓢(ModelE, ℝ)) :
    tsupport (firstOrderSchwartz a v f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  apply hx
  rw [firstOrderSchwartz_apply, fderiv_of_notMem_tsupport ℝ hxf]
  simp


theorem firstOrder_cutoffSchwartz {iota : Type*} [Fintype iota]
    (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE)
    (η : 𝓢(ModelE, ℝ)) (hη : HasCompactSupport η) {U : Set ModelE}
    (hU : IsOpen U) (hηU : tsupport η ⊆ U) (f : ModelE → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (x : ModelE) :
    firstOrderSchwartz a v (cutoffSchwartz η hη hU hηU f hf) x =
      η x * (∑ i, a i x * fderiv ℝ f x (v i)) +
        f x * firstOrderSchwartz a v η x := by
  rw [firstOrderSchwartz_apply, firstOrderSchwartz_apply]
  change (∑ i, a i x * fderiv ℝ (fun y => η y * f y) x (v i)) = _
  simp_rw [fderiv_cutoff_mul η hU hηU hf]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


def schwartzMultiplier (η : 𝓢(ModelE, ℝ)) : Lp ℝ 2 (volume : Measure ModelE) →L[ℝ]
    Lp ℝ 2 (volume : Measure ModelE) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL volume ⊤ 2 2 (η.toLp ⊤ volume)

theorem schwartzMultiplier_coe (η : 𝓢(ModelE, ℝ)) (f : Lp ℝ 2 (volume : Measure ModelE)) :
    schwartzMultiplier η f =ᵐ[volume] fun x => η x * f x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (η.toLp ⊤ volume) f,
    η.coeFn_toLp ⊤ volume] with x hmul hη
  change (ContinuousLinearMap.mul ℝ ℝ).holder 2 (η.toLp ⊤ volume) f x = _
  rw [hmul, hη]
  rfl

def cutoffL2 (η : 𝓢(ModelE, ℝ)) {U : Set ModelE} (hU : MeasurableSet U) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] Lp ℝ 2 (volume : Measure ModelE) :=
  (schwartzMultiplier η).comp (zeroExtendL2 hU).toContinuousLinearMap

theorem cutoffL2_coe (η : 𝓢(ModelE, ℝ)) {U : Set ModelE} (hU : MeasurableSet U)
    (hηU : tsupport η ⊆ U) (f : Lp ℝ 2 (volume.restrict U)) :
    cutoffL2 η hU f =ᵐ[volume] fun x => η x * f x := by
  filter_upwards [schwartzMultiplier_coe η (zeroExtendL2 hU f), zeroExtendL2_coe hU f]
    with x hmul hzero
  change schwartzMultiplier η (zeroExtendL2 hU f) x = _
  rw [hmul, hzero]
  by_cases hx : x ∈ U
  · simp [hx]
  · have hηzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηU h))
    simp [hηzero]

theorem cutoffL2_toLp_coe (η : 𝓢(ModelE, ℝ)) {U : Set ModelE} (hU : MeasurableSet U)
    (hηU : tsupport η ⊆ U) {f : ModelE → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    cutoffL2 η hU (hf.toLp f) =ᵐ[volume] fun x => η x * f x := by
  filter_upwards [cutoffL2_coe η hU hηU (hf.toLp f),
    (ae_restrict_iff' hU).mp hf.coeFn_toLp] with x hcut hfval
  rw [hcut]
  by_cases hx : x ∈ U
  · rw [hfval hx]
  · have hηzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηU h))
    simp [hηzero]

theorem cutoffL2_toLp_eq_cutoffSchwartz (η : 𝓢(ModelE, ℝ)) (hη : HasCompactSupport η)
    {U : Set ModelE} (hU : IsOpen U) (hηU : tsupport η ⊆ U) {f : ModelE → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hfLp : MemLp f 2 (volume.restrict U)) :
    cutoffL2 η hU.measurableSet (hfLp.toLp f) =
      (cutoffSchwartz η hη hU hηU f hf).toLp 2 volume := by
  apply Lp.ext
  exact (cutoffL2_toLp_coe η hU.measurableSet hηU hfLp).trans
    ((cutoffSchwartz η hη hU hηU f hf).coeFn_toLp 2 volume).symm

theorem cutoffL2_tendsto_zero (η : 𝓢(ModelE, ℝ)) {U : Set ModelE} (hU : MeasurableSet U)
    {f : ℕ → Lp ℝ 2 (volume.restrict U)} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun j => cutoffL2 η hU (f j)) atTop (𝓝 0) := by
  simpa only [map_zero, Function.comp_def] using ((cutoffL2 η hU).continuous.tendsto 0).comp hf

end PoincareConjecture.EuclideanDerivativeNative
