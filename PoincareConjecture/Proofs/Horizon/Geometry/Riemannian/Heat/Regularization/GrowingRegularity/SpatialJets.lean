import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.TimeDerivatives.Equation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Uniform











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace Poincare.Parabolic.Interior

open Analysis.Elliptic.InteriorEstimates

variable {n : ℕ} [NeZero n]
local notation "E" => EuclideanSpace ℝ (Fin n)

omit [NeZero n] in
theorem secondOrderOperator_eq_matrixLap
    (A : E → E →L[ℝ] E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ ∞ u x) :
    secondOrderOperator (fun z => coefficientMatrix (A z)) (fun _ _ => 0) u x =
      Kernel.matrixLap (coefficientMatrix (A x)) (fderiv ℝ (fderiv ℝ u) x) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  simp only [secondOrderOperator, zero_mul, Finset.sum_const_zero, add_zero,
    Kernel.matrixLap, smul_eq_mul, Analysis.Elliptic.Iteration.partialDeriv,
    EuclideanSpace.basisFun_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change coefficientMatrix (A x) i j *
      (fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem iterate_secondOrderOperator_timeDerivative_slice
    {A : E → E →L[ℝ] E} {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {O : Set E} {J : Set ℝ} (hO : IsOpen O) (hJ : IsOpen J)
    (hheat : ∀ x ∈ O, ∀ t ∈ J,
      timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (A x))
        (spatialDerivative (spatialDerivative f) (x, t)))
    (j l : ℕ) {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ O) :
    ((secondOrderOperator (fun z => coefficientMatrix (A z)) (fun _ _ => 0))^[l]
      (fun z => ((timeDerivative^[j]) f) (z, t))) x =
      ((timeDerivative^[j + l]) f) (x, t) := by
  induction l generalizing x with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply']
    have heq : ((secondOrderOperator (fun z => coefficientMatrix (A z)) (fun _ _ => 0))^[l]
        (fun z => ((timeDerivative^[j]) f) (z, t))) =ᶠ[𝓝 x]
        (fun z => ((timeDerivative^[j + l]) f) (z, t)) := by
      filter_upwards [hO.mem_nhds hx] with z hz
      exact ih hz
    rw [secondOrderOperator_eq_of_eventuallyEq _ _ heq]
    have hiter := iterate_timeDerivative_static_heat_equation hf hJ hheat (j + l)
    have hslice : ContDiff ℝ ∞ (fun z => ((timeDerivative^[j + l]) f) (z, t)) :=
      hiter.1.comp (contDiff_id.prodMk contDiff_const)
    rw [secondOrderOperator_eq_matrixLap A hslice.contDiffAt,
      fderiv_fderiv_spatialSlice hiter.1, ← hiter.2 x hx t ht]
    simp only [Nat.add_succ, Function.iterate_succ_apply']

theorem fderiv_fderiv_spatialSlice_on
    {f : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : E} {t : ℝ} (hp : (x, t) ∈ U) :
    fderiv ℝ (fderiv ℝ (fun z => f (z, t))) x =
      spatialDerivative (spatialDerivative f) (x, t) := by
  obtain ⟨v, hv, _, hvf⟩ := exists_compact_smooth_extension
    (isCompact_singleton (x := (x, t))) hU (singleton_subset_iff.mpr hp) hf
  have heq := hvf (x, t) (by simp)
  rw [← fderiv_fderiv_spatialSlice_eq_of_eventuallyEq heq,
    fderiv_fderiv_spatialSlice hv]
  exact (spatialDerivative_eventuallyEq (spatialDerivative_eventuallyEq heq)).eq_of_nhds

theorem iterate_secondOrderOperator_timeDerivative_slice_on
    {A : E → E →L[ℝ] E} {f : E × ℝ → ℝ}
    {O : Set E} {J : Set ℝ} (hO : IsOpen O) (hJ : IsOpen J)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ J))
    (hheat : ∀ x ∈ O, ∀ t ∈ J,
      timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (A x))
        (spatialDerivative (spatialDerivative f) (x, t)))
    (j l : ℕ) {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ O) :
    ((secondOrderOperator (fun z => coefficientMatrix (A z)) (fun _ _ => 0))^[l]
      (fun z => ((timeDerivative^[j]) f) (z, t))) x =
      ((timeDerivative^[j + l]) f) (x, t) := by
  induction l generalizing x with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply']
    have heq : ((secondOrderOperator (fun z => coefficientMatrix (A z)) (fun _ _ => 0))^[l]
        (fun z => ((timeDerivative^[j]) f) (z, t))) =ᶠ[𝓝 x]
        (fun z => ((timeDerivative^[j + l]) f) (z, t)) := by
      filter_upwards [hO.mem_nhds hx] with z hz
      exact ih hz
    rw [secondOrderOperator_eq_of_eventuallyEq _ _ heq]
    have hiter := iterate_timeDerivative_static_heat_equation_on hO hJ hf hheat (j + l)
    have hslice : ContDiffOn ℝ ∞ (fun z => ((timeDerivative^[j + l]) f) (z, t)) O :=
      hiter.1.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
    rw [secondOrderOperator_eq_matrixLap A (hslice.contDiffAt (hO.mem_nhds hx)),
      fderiv_fderiv_spatialSlice_on (hO.prod hJ) hiter.1 ⟨hx, ht⟩,
      ← hiter.2 x hx t ht]
    simp only [Nat.add_succ, Function.iterate_succ_apply']



theorem exists_spatial_jet_bound_of_bounded_powers
    {O V K : Set E} (hO : IsOpen O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hK : IsCompact K) (hKV : K ⊆ V)
    (a : E → Matrix (Fin n) (Fin n) ℝ) (b : Fin n → E → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hpos : ∀ x ∈ O, (a x).PosDef)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) O) (m : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 0 ≤ B →
      ∀ {u : E → ℝ}, ContDiffOn ℝ ∞ u O →
      (∀ j ≤ q, ∀ x ∈ V, |((secondOrderOperator a b)^[j] u) x| ≤ B) →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ m u x‖ ≤ C * B := by
  obtain ⟨q, C, hC, hjet⟩ := uniform_interior_estimate_of_elliptic_powers
    hO hV hVc hVO hK hKV a b ha hpos hb m
  have hVfin : volume V ≠ ⊤ := (lt_of_le_of_lt (measure_mono subset_closure)
    hVc.measure_lt_top).ne
  let W : ℝ := ((volume V) ^ ((2 : ℝ≥0∞).toReal)⁻¹).toReal
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  refine ⟨q, C * ((q + 1 : ℕ) : ℝ) * (W + 1), by positivity, ?_⟩
  intro B hB u hu hp x hx
  have hl2 (j : ℕ) (hj : j ≤ q) :
      (eLpNorm ((secondOrderOperator a b)^[j] u) 2 (volume.restrict V)).toReal ≤ W * B := by
    have hbound : ∀ᵐ z ∂volume.restrict V,
        ‖((secondOrderOperator a b)^[j] u) z‖ ≤ B := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      exact hp j hj z hz
    have he := eLpNorm_le_of_ae_bound (p := 2) hbound
    rw [Measure.restrict_apply_univ] at he
    have hfinite : (volume V) ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ENNReal.ofReal B ≠ ⊤ := by
      apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hVfin
    have he' := ENNReal.toReal_mono hfinite he
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, W] using he'
  apply (hjet hu x hx).trans
  calc
    C * ∑ j ∈ Finset.range (q + 1),
        (eLpNorm ((secondOrderOperator a b)^[j] u) 2 (volume.restrict V)).toReal ≤
        C * ∑ _j ∈ Finset.range (q + 1), W * B := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Finset.sum_le_sum (fun j hj => hl2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = C * ((q + 1 : ℕ) : ℝ) * W * B := by simp [Finset.sum_const, mul_assoc]
    _ ≤ C * ((q + 1 : ℕ) : ℝ) * (W + 1) * B := by gcongr; linarith

end Poincare.Parabolic.Interior
