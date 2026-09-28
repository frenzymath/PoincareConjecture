import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.FrozenEvolution
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.LowerDerivatives

noncomputable section

open Asymptotics Filter Matrix MeasureTheory Real Set
open scoped NNReal RealInnerProductSpace Topology

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem heatScaled_integrable (t : Real)
    (u : BoundedContinuousFunction V F) (x : V) :
    Integrable (fun z : V ↦ baseHeat z • u (x - heatScale t • z)) := by
  refine ((baseHeat_int (V := V)).norm.mul_const ‖u‖).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold baseHeat heatScale
    fun_prop
  · filter_upwards with z
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (norm_nonneg _)

omit [CompleteSpace F] in
theorem heatScaled_add
    (t : Real) (u v : BoundedContinuousFunction V F) (x : V) :
    heatScaled t (u + v) x = heatScaled t u x + heatScaled t v x := by
  unfold heatScaled
  rw [← integral_add (heatScaled_integrable t u x)
    (heatScaled_integrable t v x)]
  apply integral_congr_ae
  filter_upwards with z
  change baseHeat z • (u (x - heatScale t • z) +
    v (x - heatScale t • z)) = _
  rw [smul_add]

omit [CompleteSpace F] in
theorem heatScaled_sub
    (t : Real) (u v : BoundedContinuousFunction V F) (x : V) :
    heatScaled t (u - v) x = heatScaled t u x - heatScaled t v x := by
  unfold heatScaled
  rw [← integral_sub (heatScaled_integrable t u x)
    (heatScaled_integrable t v x)]
  apply integral_congr_ae
  filter_upwards with z
  change baseHeat z • (u (x - heatScale t • z) -
    v (x - heatScale t • z)) = _
  rw [smul_sub]

omit [Nontrivial V] [CompleteSpace F] in
theorem heatScaled_smul
    (t c : Real) (u : BoundedContinuousFunction V F) (x : V) :
    heatScaled t (c • u) x = c • heatScaled t u x := by
  unfold heatScaled
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  change baseHeat z • (c • u (x - heatScale t • z)) =
    c • (baseHeat z • u (x - heatScale t • z))
  exact smul_comm _ _ _

omit [Nontrivial V] [CompleteSpace F] in
@[simp]
theorem heatScaled_zero_bcf
    (t : Real) (x : V) :
    heatScaled t (0 : BoundedContinuousFunction V F) x = 0 := by
  have h := heatScaled_smul t 0
    (0 : BoundedContinuousFunction V F) x
  simpa only [zero_smul] using h

omit [CompleteSpace F] in
theorem tendsto_heatScaled_of_tendsto
    {A : Type*} {l : Filter A} {q : A → Real} {q₀ : Real}
    {u : A → BoundedContinuousFunction V F}
    {u₀ : BoundedContinuousFunction V F}
    (hq : Tendsto q l (nhds q₀)) (hu : Tendsto u l (nhds u₀)) (x : V) :
    Tendsto (fun a ↦ heatScaled (q a) (u a) x) l
      (nhds (heatScaled q₀ u₀ x)) := by
  have hdiff : Tendsto (fun a ↦ u a - u₀) l (nhds 0) := by
    simpa only [sub_self] using hu.sub
      (tendsto_const_nhds : Tendsto (fun _ : A ↦ u₀) l (nhds u₀))
  have hnorm : Tendsto (fun a ↦ ‖u a - u₀‖) l (nhds 0) := by
    simpa only [norm_zero] using hdiff.norm
  have hscaledNorm : Tendsto
      (fun a ↦ ‖heatScaled (q a) (u a - u₀) x‖) l (nhds 0) := by
    exact squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _)
      (Eventually.of_forall fun a ↦ heatScaled_norm _ _ _) hnorm
  have hscaledZero : Tendsto
      (fun a ↦ heatScaled (q a) (u a - u₀) x) l (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hscaledNorm
  have hfixed : Tendsto (fun a ↦ heatScaled (q a) u₀ x) l
      (nhds (heatScaled q₀ u₀ x)) :=
    (heatScaled_cont u₀ x).tendsto q₀ |>.comp hq
  convert hscaledZero.add hfixed using 1
  · funext a
    rw [← heatScaled_add]
    congr 2
    abel
  · simp only [zero_add]

omit [CompleteSpace F] in
theorem heatScaled_sub_time_hasDerivAt
    {t s : Real} (hst : s < t)
    (u dtU : Real → BoundedContinuousFunction V F)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (d2u : Real →
      BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (huTime : HasDerivAt u (dtU s) s)
    (hu : ∀ x, HasFDerivAt (u s : V → F) (du s x) x)
    (hdu : ∀ x, HasFDerivAt
      (du s : V → V →L[Real] F) (d2u s x) x)
    (x : V) :
    HasDerivAt (fun r ↦ heatScaled (t - r) (u r) x)
      (heatScaled (t - s) (dtU s) x -
        heatScaled (t - s) (coreLap (d2u s)) x) s := by
  let q : Real → Real := fun r ↦ t - r
  let R : Real → BoundedContinuousFunction V F := fun r ↦
    u r - u s - (r - s) • dtU s
  let D : Real → F := fun r ↦
    heatScaled (q r) (dtU s) x - heatScaled (q s) (dtU s) x
  have hq : HasDerivAt q (-1) s := by
    have hraw := (hasDerivAt_const s t).sub (hasDerivAt_id s)
    refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ ?_)).congr_deriv ?_
    · rfl
    · ring
  have htime : HasDerivAt
      (fun r ↦ heatScaled (q r) (u s) x)
      (-heatScaled (q s) (coreLap (d2u s)) x) s := by
    have hpositive : HasDerivAt
        (fun z ↦ heatScaled z (u s) x)
        (heatScaled (q s) (coreLap (d2u s)) x) (q s) := by
      have hraw := heatSup_time (sub_pos.mpr hst)
        (u s) (du s) (d2u s) hu hdu x
      have heq : (fun z ↦ heatScaled z (u s) x) =ᶠ[nhds (q s)]
          fun z ↦ heatSup z (u s) x := by
        filter_upwards [Ioi_mem_nhds (sub_pos.mpr hst)] with z hz
        exact (heatSup_scaled hz (u s) x).symm
      have hconverted := hraw.congr_of_eventuallyEq heq
      exact hconverted.congr_deriv
        (heatSup_scaled (sub_pos.mpr hst) (coreLap (d2u s)) x)
    have hraw := hpositive.scomp s hq
    refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ ?_)).congr_deriv ?_
    · rfl
    · simp only [neg_one_smul]
  have hR : R =o[nhds s] fun r ↦ r - s := by
    simpa only [R] using huTime.isLittleO
  have hscaledR : (fun r ↦ heatScaled (q r) (R r) x) =o[nhds s]
      fun r ↦ r - s := by
    apply (IsBigO.of_bound' (Eventually.of_forall fun r ↦
      heatScaled_norm (q r) (R r) x)).trans_isLittleO hR
  have hDlim : Tendsto D (nhds s) (nhds 0) := by
    have hqTend : Tendsto q (nhds s) (nhds (q s)) := hq.continuousAt
    have hheat := (heatScaled_cont (dtU s) x).tendsto (q s) |>.comp hqTend
    convert hheat.sub_const (heatScaled (q s) (dtU s) x) using 1
    · rfl
    · simp only [sub_self]
  have hDo : D =o[nhds s] fun _ ↦ (1 : Real) :=
    (isLittleO_one_iff Real).mpr hDlim
  have hcross : (fun r ↦ (r - s) • D r) =o[nhds s]
      fun r ↦ r - s := by
    simpa only [smul_eq_mul, mul_one] using
      (isBigO_refl (fun r ↦ r - s) (nhds s)).smul_isLittleO hDo
  apply HasDerivAt.of_isLittleO
  have hsum := htime.isLittleO.add (hscaledR.add hcross)
  apply hsum.congr'
  · apply Eventually.of_forall
    intro r
    have hRscaled : heatScaled (q r) (R r) x =
        heatScaled (q r) (u r) x - heatScaled (q r) (u s) x -
          (r - s) • heatScaled (q r) (dtU s) x := by
      dsimp only [R]
      rw [heatScaled_sub, heatScaled_sub, heatScaled_smul]
    change
      heatScaled (q r) (u s) x - heatScaled (q s) (u s) x -
          (r - s) • (-heatScaled (q s) (coreLap (d2u s)) x) +
        (heatScaled (q r) (R r) x + (r - s) • D r) =
      heatScaled (t - r) (u r) x - heatScaled (t - s) (u s) x -
        (r - s) • (heatScaled (t - s) (dtU s) x -
          heatScaled (t - s) (coreLap (d2u s)) x)
    rw [hRscaled]
    dsimp only [D, q]
    simp only [smul_sub, smul_neg]
    abel
  · exact Eventually.of_forall fun _ ↦ rfl

theorem heatDuh_eq_of_zero_initial
    {t : Real} (ht : 0 < t)
    (u dtU : Real → BoundedContinuousFunction V F)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (d2u : Real →
      BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (huTime : ∀ s ∈ Ioo (0 : Real) t, HasDerivAt u (dtU s) s)
    (hu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (u s : V → F) (du s x) x)
    (hdu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (du s : V → V →L[Real] F) (d2u s x) x)
    (huCont : Continuous u) (hu0 : u 0 = 0)
    (x : V)
    (hint : IntervalIntegrable
      (fun s ↦ heatScaled (t - s) (dtU s - coreLap (d2u s)) x)
      volume 0 t) :
    heatDuh t (fun s ↦ dtU s - coreLap (d2u s)) x = u t x := by
  let source : Real → BoundedContinuousFunction V F :=
    fun s ↦ dtU s - coreLap (d2u s)
  let w : Real → F := fun s ↦ heatScaled (t - s) (u s) x
  have hwderiv : ∀ s ∈ Ioo (0 : Real) t,
      HasDerivAt w (heatScaled (t - s) (source s) x) s := by
    intro s hs
    have h := heatScaled_sub_time_hasDerivAt hs.2 u dtU du d2u
      (huTime s hs) (hu s hs) (hdu s hs) x
    simpa only [w, source, heatScaled_sub] using h
  have hleft : Tendsto w (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hq : Tendsto (fun s : Real ↦ t - s) (nhdsWithin 0 (Ioi 0))
        (nhds t) := by
      have hc : ContinuousAt (fun s : Real ↦ t - s) 0 :=
        continuousAt_const.sub continuousAt_id
      simpa only [sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have huT : Tendsto u (nhdsWithin 0 (Ioi 0)) (nhds (u 0)) :=
      huCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h := tendsto_heatScaled_of_tendsto hq huT x
    simpa only [w, hu0, heatScaled_zero_bcf] using h
  have hright : Tendsto w (nhdsWithin t (Iio t)) (nhds (u t x)) := by
    have hq : Tendsto (fun s : Real ↦ t - s) (nhdsWithin t (Iio t))
        (nhds 0) := by
      have hc : ContinuousAt (fun s : Real ↦ t - s) t :=
        continuousAt_const.sub continuousAt_id
      simpa only [sub_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have huT : Tendsto u (nhdsWithin t (Iio t)) (nhds (u t)) :=
      huCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h := tendsto_heatScaled_of_tendsto hq huT x
    simpa only [w, heatScaled_zero] using h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    ht hwderiv (by simpa only [source] using hint) hleft hright
  unfold heatDuh
  rw [show (∫ s : Real in 0..t, heatSup (t - s) (source s) x) =
      ∫ s : Real in 0..t, heatScaled (t - s) (source s) x by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hst
    intro hs
    rw [uIoc_of_le ht.le] at hs
    exact heatSup_scaled (sub_pos.mpr (lt_of_le_of_ne hs.2 hst))
      (source s) x]
  simpa only [source, sub_zero] using hftc

end Poincare.Parabolic.Interior.Kernel
