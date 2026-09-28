import PoincareConjecture.Proofs.M35.RadialGauge.GaussianTrace
import PoincareConjecture.Proofs.M35.RadialGauge.HeatTimeDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



noncomputable def euclideanLaplacian (f : V → F) (x : V) : F :=
  ∑ i : Fin (n + 1), fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single i (1 : ℝ))



theorem heatAverage_hasDerivAt_trace {f : V → F} {f' : V → V →L[ℝ] F}
    {f'' : V → V →L[ℝ] V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ x, HasFDerivAt f (f' x) x) (hdd : ∀ x, HasFDerivAt f' (f'' x) x)
    {C D E : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖f' x‖ ≤ D)
    (hddb : ∀ x, ‖f'' x‖ ≤ E) {t : ℝ} (ht : 0 < t) (x : V) :
    HasDerivAt (fun s => heatAverage s f x)
      (heatAverage t (fun y => ∑ i : Fin (n + 1), f'' y
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) x) t := by
  let a := Real.sqrt (2 * t)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hc : Continuous (fun z : V => x + a • z) := by fun_prop
  have hshift (z : V) : HasFDerivAt (fun w : V => f' (x + a • w))
      (a • f'' (x + a • z)) z := by
    simpa only [Function.comp_def, Pi.smul_apply, id_eq,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using
      (hdd _).comp z (((hasFDerivAt_id z).const_smul a).const_add x)
  have htrace := integral_stdGaussian_covector_trace
    (hf'.comp hc) ((hf''.comp hc).const_smul a) hshift
    (fun z => hdb (x + a • z)) (D := a * E) (fun z => by
      change ‖a • f'' (x + a • z)‖ ≤ a * E
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left (hddb _) ha.le)
  simp only [Function.comp_def, Pi.smul_apply] at htrace
  have heq : a⁻¹ • (∫ z, f' (x + a • z) z ∂stdGaussian V) =
      heatAverage t (fun y => ∑ i : Fin (n + 1), f'' y
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) x := by
    rw [htrace]
    simp only [smul_apply, ← Finset.smul_sum, integral_smul, inv_smul_smul₀ ha.ne']
    rfl
  rw [← heq]
  exact heatAverage_hasDerivAt_time_integral hf hf' hd hb hdb ht x



theorem euclideanLaplacian_heatAverage {f : V → F} {f' : V → V →L[ℝ] F}
    {f'' : V → V →L[ℝ] V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ x, HasFDerivAt f (f' x) x) (hdd : ∀ x, HasFDerivAt f' (f'' x) x)
    {C D E : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖f' x‖ ≤ D)
    (hddb : ∀ x, ‖f'' x‖ ≤ E) (t : ℝ) (x : V) :
    euclideanLaplacian (heatAverage t f) x =
      heatAverage t (fun y => ∑ i : Fin (n + 1), f'' y
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) x := by
  have hd1 : fderiv ℝ (heatAverage t f) = heatAverage t f' :=
    funext (fun y => (heatAverage_hasFDerivAt_of_bounds hf hf' hd hb hdb t y).fderiv)
  have hd2 : fderiv ℝ (fderiv ℝ (heatAverage t f)) = heatAverage t f'' := by
    rw [hd1]
    exact funext (fun y => (heatAverage_hasFDerivAt_of_bounds hf' hf'' hdd hdb hddb t y).fderiv)
  let e (i : Fin (n + 1)) := EuclideanSpace.single i (1 : ℝ)
  have hi := heatAverage_integrable_of_bound (f := f'') hf'' hddb t x
  have hia (i : Fin (n + 1)) : Integrable
      (fun z => f'' (x + Real.sqrt (2 * t) • z) (e i)) (stdGaussian V) :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] F) (e i)).integrable_comp hi
  have hiaa (i : Fin (n + 1)) : Integrable
      (fun z => f'' (x + Real.sqrt (2 * t) • z) (e i) (e i)) (stdGaussian V) :=
    (ContinuousLinearMap.apply ℝ F (e i)).integrable_comp (hia i)
  unfold euclideanLaplacian
  rw [hd2]
  change (∑ i, (∫ z, f'' (x + Real.sqrt (2 * t) • z) ∂stdGaussian V) (e i) (e i)) = _
  calc
    _ = ∑ i, ∫ z, f'' (x + Real.sqrt (2 * t) • z) (e i) (e i) ∂stdGaussian V := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ContinuousLinearMap.integral_apply hi, ContinuousLinearMap.integral_apply (hia i)]
    _ = _ := (integral_finsetSum _ (fun i _ => hiaa i)).symm



theorem heatAverage_solves_heat {f : V → F} {f' : V → V →L[ℝ] F}
    {f'' : V → V →L[ℝ] V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ x, HasFDerivAt f (f' x) x) (hdd : ∀ x, HasFDerivAt f' (f'' x) x)
    {C D E : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖f' x‖ ≤ D)
    (hddb : ∀ x, ‖f'' x‖ ≤ E) {t : ℝ} (ht : 0 < t) (x : V) :
    HasDerivAt (fun s => heatAverage s f x) (euclideanLaplacian (heatAverage t f) x) t := by
  rw [euclideanLaplacian_heatAverage hf hf' hf'' hd hdd hb hdb hddb]
  exact heatAverage_hasDerivAt_trace hf hf' hf'' hd hdd hb hdb hddb ht x

end PoincareConjecture.M35.RadialGauge
