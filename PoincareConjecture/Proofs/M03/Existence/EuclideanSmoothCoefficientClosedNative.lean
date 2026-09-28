import PoincareConjecture.Proofs.M03.Existence.EuclideanLocalClosedNative
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped Topology ENNReal SchwartzMap ContDiff

noncomputable section

namespace PoincareConjecture.EuclideanDerivativeNative

variable {n : ℕ}

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

def schwartzMultiplierMeasure (μ : Measure ModelE) (η : 𝓢(ModelE, ℝ)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ⊤ 2 2
    ((η.toBoundedContinuousFunction.memLp_top (μ := μ)).toLp η.toBoundedContinuousFunction)

theorem schwartzMultiplierMeasure_coe (μ : Measure ModelE) (η : 𝓢(ModelE, ℝ))
    (f : Lp ℝ 2 μ) : schwartzMultiplierMeasure μ η f =ᵐ[μ] fun x => η x * f x := by
  let ηLp : Lp ℝ ⊤ μ :=
    (η.toBoundedContinuousFunction.memLp_top (μ := μ)).toLp η.toBoundedContinuousFunction
  have hηLp : ηLp =ᵐ[μ] η := (η.toBoundedContinuousFunction.memLp_top (μ := μ)).coeFn_toLp
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) ηLp f, hηLp]
    with x hmul hη
  change (ContinuousLinearMap.mul ℝ ℝ).holder 2 ηLp f x = _
  rw [hmul, hη]
  rfl

theorem schwartzMultiplierMeasure_toLp_coe (μ : Measure ModelE) (η : 𝓢(ModelE, ℝ))
    {f : ModelE → ℝ} (hf : MemLp f 2 μ) :
    schwartzMultiplierMeasure μ η (hf.toLp f) =ᵐ[μ] fun x => η x * f x := by
  filter_upwards [schwartzMultiplierMeasure_coe μ η (hf.toLp f), hf.coeFn_toLp]
    with x hmul hfval
  rw [hmul, hfval]

variable {iota : Type*} [Fintype iota]

theorem local_smoothFirstOrder_limit_zero {U : Set ModelE} (hU : IsOpen U)
    (a : iota → ModelE → ℝ) (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (v : iota → ModelE)
    (f : ℕ → ModelE → ℝ) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U)
    (hfLp : ∀ j, MemLp (f j) 2 (volume.restrict U))
    (hAfLp : ∀ j, MemLp (fun x => ∑ i, a i x * fderiv ℝ (f j) x (v i))
      2 (volume.restrict U))
    (w : Lp ℝ 2 (volume.restrict U))
    (hflim : Tendsto (fun j => (hfLp j).toLp (f j)) atTop (𝓝 0))
    (hAflim : Tendsto (fun j => (hAfLp j).toLp
      (fun x => ∑ i, a i x * fderiv ℝ (f j) x (v i))) atTop (𝓝 w)) : w = 0 := by
  apply Lp.ext
  apply (ae_zero_of_compact_cutoffs hU ?_).trans (Lp.coeFn_zero ℝ 2 (volume.restrict U)).symm
  intro η hη hηU
  let b : iota → 𝓢(ModelE, ℝ) := fun i => cutoffSchwartz η hη hU hηU (a i) (ha i)
  let mult : Lp ℝ 2 (volume.restrict U) →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
    schwartzMultiplierMeasure (volume.restrict U) η
  let V : ℕ → Lp ℝ 2 (volume.restrict U) := fun j =>
    mult ((hAfLp j).toLp (fun x => ∑ i, a i x * fderiv ℝ (f j) x (v i)))
  have hformula (j : ℕ) (x : ModelE) :
      (∑ i, b i x * fderiv ℝ (f j) x (v i)) =
        η x * (∑ i, a i x * fderiv ℝ (f j) x (v i)) := by
    change (∑ i, (η x * a i x) * fderiv ℝ (f j) x (v i)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hV (j : ℕ) : V j =ᵐ[volume.restrict U]
      (fun x => ∑ i, b i x * fderiv ℝ (f j) x (v i)) :=
    (schwartzMultiplierMeasure_toLp_coe (volume.restrict U) η (hAfLp j)).trans
      (Eventually.of_forall (fun x => (hformula j x).symm))
  have hBfLp (j : ℕ) : MemLp (fun x => ∑ i, b i x * fderiv ℝ (f j) x (v i))
      2 (volume.restrict U) := MemLp.ae_eq (hV j) (Lp.memLp (V j))
  have hVeq (j : ℕ) : V j =
      (hBfLp j).toLp (fun x => ∑ i, b i x * fderiv ℝ (f j) x (v i)) := by
    apply Lp.ext
    exact (hV j).trans (hBfLp j).coeFn_toLp.symm
  have hBflim : Tendsto (fun j => (hBfLp j).toLp
      (fun x => ∑ i, b i x * fderiv ℝ (f j) x (v i))) atTop (𝓝 (mult w)) := by
    have hmult : Tendsto V atTop (𝓝 (mult w)) := by
      simpa only [V, Function.comp_def] using (mult.continuous.tendsto w).comp hAflim
    exact hmult.congr' (Eventually.of_forall hVeq)
  have hzero : mult w = 0 :=
    local_firstOrder_limit_zero b v hU f hf hfLp hBfLp (mult w) hflim hBflim
  have hprod : (fun x => η x * w x) =ᵐ[volume.restrict U] 0 := by
    have hcoe := schwartzMultiplierMeasure_coe (volume.restrict U) η w
    change mult w =ᵐ[volume.restrict U] (fun x => η x * w x) at hcoe
    rw [hzero] at hcoe
    exact hcoe.symm.trans (Lp.coeFn_zero ℝ 2 (volume.restrict U))
  filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hprod] with x hxprod
  by_cases hx : x ∈ U
  · exact hxprod hx
  · have hηzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηU h))
    simp [hηzero]

end PoincareConjecture.EuclideanDerivativeNative
