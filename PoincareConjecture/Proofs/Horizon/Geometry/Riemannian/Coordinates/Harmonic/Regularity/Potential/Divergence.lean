import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactPotential










noncomputable section
set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ContDiff Topology BigOperators

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem continuous_heatScaled_time {f : ℝ → BoundedContinuousFunction V F}
    (hf : Continuous f) (t : ℝ) (x : V) :
    Continuous (fun s => heatScaled (t - s) (f s) x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact tendsto_heatScaled_of_tendsto
    (continuous_const.sub continuous_id).continuousAt hf.continuousAt x


theorem heatDuh_sub_of_continuous {t : ℝ} (ht : 0 < t)
    (f q : ℝ → BoundedContinuousFunction V F) (hf : Continuous f) (hq : Continuous q)
    (x : V) :
    heatDuh t (fun s => f s - q s) x = heatDuh t f x - heatDuh t q x := by
  simp only [heatDuh_eq_integral_heatScaled ht, heatScaled_sub]
  exact intervalIntegral.integral_sub
    ((continuous_heatScaled_time hf t x).intervalIntegrable 0 t)
    ((continuous_heatScaled_time hq t x).intervalIntegrable 0 t)

private theorem heatScaled_sum {ι : Type*} (s : Finset ι) (t : ℝ)
    (f : ι → BoundedContinuousFunction V F) (x : V) :
    heatScaled t (∑ i ∈ s, f i) x = ∑ i ∈ s, heatScaled t (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [heatScaled]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, heatScaled_add, ih]


theorem heatDuh_sum_of_continuous {ι : Type*} {t : ℝ} (ht : 0 < t) (s : Finset ι)
    (f : ι → ℝ → BoundedContinuousFunction V F) (hf : ∀ i ∈ s, Continuous (f i))
    (x : V) :
    heatDuh t (fun r => ∑ i ∈ s, f i r) x = ∑ i ∈ s, heatDuh t (f i) x := by
  simp only [heatDuh_eq_integral_heatScaled ht, heatScaled_sum]
  exact intervalIntegral.integral_finsetSum
    (fun i hi => (continuous_heatScaled_time (hf i hi) t x).intervalIntegrable 0 t)


theorem heatDuh_map_of_continuous [CompleteSpace F] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {t : ℝ} (ht : 0 < t) (L : F →L[ℝ] G)
    (f : ℝ → BoundedContinuousFunction V F) (hf : Continuous f) (x : V) :
    L (heatDuh t f x) = heatDuh t (fun s => L.compLeftContinuousBounded V (f s)) x := by
  simp only [heatDuh_eq_integral_heatScaled ht]
  rw [← L.intervalIntegral_comp_comm
    ((continuous_heatScaled_time hf t x).intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact heatScaled_map L (t - s) (f s) x

end Poincare.Parabolic.Interior.Kernel

namespace Poincare.Parabolic.Interior

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in

theorem contDiff_spatialDirectional {f : V × ℝ → F} (hf : ContDiff ℝ ∞ f) (v : V) :
    ContDiff ℝ ∞ (fun p => spatialDerivative f p v) :=
  (contDiff_spatialDerivative hf).clm_apply contDiff_const

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in

theorem hasCompactSupport_spatialDirectional {f : V × ℝ → F}
    (hc : HasCompactSupport f) (v : V) :
    HasCompactSupport (fun p => spatialDerivative f p v) :=
  (hasCompactSupport_spatialDerivative hc).comp_left (g := fun L : V →L[ℝ] F => L v) (by simp)



theorem heatDuh_compactSlice_spatialDirectional {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (x v : V) :
    Kernel.heatDuh t
      (compactSlice (fun p => spatialDerivative f p v)
        (contDiff_spatialDirectional hf v).continuous
        (hasCompactSupport_spatialDirectional hc v)) x =
      fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) x v := by
  rw [(hasFDerivAt_heatDuh_compactSlice hf hc ht x).fderiv]
  let L : (V →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F v
  let du := compactSlice (spatialDerivative f) (contDiff_spatialDerivative hf).continuous
    (hasCompactSupport_spatialDerivative hc)
  change _ = L (Kernel.heatDuh t du x)
  rw [Kernel.heatDuh_map_of_continuous ht L du
    (continuous_compactSlice (contDiff_spatialDerivative hf) (hasCompactSupport_spatialDerivative hc))]
  congr 1




theorem eq_heatDuh_sub_sum_fderiv_of_residual_divergence {ι : Type*} [Fintype ι]
    {w f : V × ℝ → F} (q : ι → V × ℝ → F) (e : ι → V)
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (hzero : ∀ x, w (x, 0) = 0)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hq : ∀ i, ContDiff ℝ ∞ (q i)) (hqc : ∀ i, HasCompactSupport (q i))
    (hres : ∀ p, heatResidual w p = f p - ∑ i, spatialDerivative (q i) p (e i))
    {t : ℝ} (ht : 0 < t) (x : V) :
    w (x, t) = Kernel.heatDuh t (compactSlice f hf.continuous hfc) x -
      ∑ i, fderiv ℝ (Kernel.heatDuh t (compactSlice (q i) (hq i).continuous (hqc i))) x (e i) := by
  classical
  let P := compactSlice f hf.continuous hfc
  let Q := fun i => compactSlice (fun p => spatialDerivative (q i) p (e i))
    (contDiff_spatialDirectional (hq i) (e i)).continuous
    (hasCompactSupport_spatialDirectional (hqc i) (e i))
  have hQ (i) : Continuous (Q i) :=
    continuous_compactSlice (contDiff_spatialDirectional (hq i) (e i))
      (hasCompactSupport_spatialDirectional (hqc i) (e i))
  have hsource : compactSlice (heatResidual w) (contDiff_heatResidual hw).continuous
      (hasCompactSupport_heatResidual hwc) = fun s => P s - ∑ i, Q i s := by
    funext s
    ext y
    simpa only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sum_apply,
      compactSlice_apply, P, Q] using hres (y, s)
  rw [← heatDuh_compactSlice_residual hw hwc hzero ht x, hsource]
  rw [Kernel.heatDuh_sub_of_continuous ht P (fun s => ∑ i, Q i s)
    (continuous_compactSlice hf hfc) (continuous_finsetSum _ fun i _ => hQ i)]
  rw [Kernel.heatDuh_sum_of_continuous ht Finset.univ Q (fun i _ => hQ i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact heatDuh_compactSlice_spatialDirectional (hq i) (hqc i) ht x (e i)

end Poincare.Parabolic.Interior
