import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelTimeDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem euclideanLaplacian_heatDuhamel {f : ℝ → V → F} {C D E t : ℝ}
    (ht : 0 ≤ t) (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s, ContDiff ℝ 2 (f s))
    (hb : ∀ s x, ‖f s x‖ ≤ C)
    (hdb : ∀ s x, ‖fderiv ℝ (f s) x‖ ≤ D)
    (hddb : ∀ s x, ‖fderiv ℝ (fderiv ℝ (f s)) x‖ ≤ E) (x : V) :
    euclideanLaplacian (heatDuhamel f t) x =
      heatDuhamel (fun s => euclideanLaplacian (f s)) t x := by
  have hdf (s : ℝ) : ContDiff ℝ 1 (fderiv ℝ (f s)) :=
    (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) (f s) from hf s)).2.2
  have hdm := spatial_fderiv_stronglyMeasurable hfm
    (fun s => (hf s).differentiable (by norm_num))
  have hddm := spatial_fderiv_stronglyMeasurable hdm
    (fun s => (hdf s).differentiable (by norm_num))
  have hd1 := heatDuhamel_fderiv_commutes ht hfm hdm
    (fun s _ => (hf s).of_le (by norm_num)) (fun s _ => hb s) (fun s _ => hdb s)
  have hd2 : fderiv ℝ (fderiv ℝ (heatDuhamel f t)) =
      heatDuhamel (fun s => fderiv ℝ (fderiv ℝ (f s))) t := by
    rw [hd1]
    exact heatDuhamel_fderiv_commutes ht hdm hddm
      (fun s _ => hdf s) (fun s _ => hdb s) (fun s _ => hddb s)
  let e (i : Fin (n + 1)) := EuclideanSpace.single i (1 : ℝ)
  let tr : (V →L[ℝ] V →L[ℝ] F) →L[ℝ] F :=
    ∑ i : Fin (n + 1), (ContinuousLinearMap.apply ℝ F (e i)).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] F) (e i))
  have htr (A : V →L[ℝ] V →L[ℝ] F) : tr A = ∑ i, A (e i) (e i) := by
    simp [tr]
  let H (s : ℝ) := heatAverage (t - s) (fderiv ℝ (fderiv ℝ (f s))) x
  have hi : IntervalIntegrable H volume 0 t := by
    let : IsFiniteMeasure ((volume : Measure ℝ).restrict (uIoc 0 t)) := by
      rw [uIoc_of_le ht]
      infer_instance
    rw [intervalIntegrable_iff]
    exact (integrable_const E).mono'
      (heatAverage_time_stronglyMeasurable hddm t x).aestronglyMeasurable
      (Eventually.of_forall (fun s => heatAverage_norm_le
        ((hdf s).continuous_fderiv (by norm_num)) (hddb s) (t - s) x))
  unfold euclideanLaplacian
  rw [hd2]
  change (∑ i, (∫ s in 0..t, H s) (e i) (e i)) = _
  rw [← htr, ← tr.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro s _
  have hgi := heatAverage_integrable_of_bound
    (f := fderiv ℝ (fderiv ℝ (f s)))
    ((hdf s).continuous_fderiv (by norm_num)) (hddb s) (t - s) x
  change tr (∫ z, fderiv ℝ (fderiv ℝ (f s))
    (x + Real.sqrt (2 * (t - s)) • z) ∂stdGaussian V) = _
  rw [← tr.integral_comp_comm hgi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => htr _)



theorem heatDuhamel_solves_heat {f : ℝ → V → F} {C D E t : ℝ}
    (ht : 0 ≤ t) (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s, ContDiff ℝ 2 (f s))
    (hb : ∀ s x, ‖f s x‖ ≤ C)
    (hdb : ∀ s x, ‖fderiv ℝ (f s) x‖ ≤ D)
    (hddb : ∀ s x, ‖fderiv ℝ (fderiv ℝ (f s)) x‖ ≤ E)
    (x : V) (htime : ContinuousAt (fun s => f s x) t) :
    HasDerivAt (fun a => heatDuhamel f a x)
      (euclideanLaplacian (heatDuhamel f t) x + f t x) t := by
  rw [euclideanLaplacian_heatDuhamel ht hfm hf hb hdb hddb]
  exact heatDuhamel_hasDerivAt_time_trace ht hfm hf hb hdb hddb x htime

end PoincareConjecture.M35.RadialGauge
