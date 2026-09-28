import PoincareConjecture.Proofs.M35.RadialGauge.MovingTimeIntegral
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem heatDuhamel_hasDerivAt_time_trace {f : ℝ → V → F} {C D E t : ℝ}
    (ht : 0 ≤ t) (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s, ContDiff ℝ 2 (f s))
    (hb : ∀ s x, ‖f s x‖ ≤ C)
    (hdb : ∀ s x, ‖fderiv ℝ (f s) x‖ ≤ D)
    (hddb : ∀ s x, ‖fderiv ℝ (fderiv ℝ (f s)) x‖ ≤ E)
    (x : V) (htime : ContinuousAt (fun s => f s x) t) :
    HasDerivAt (fun a => heatDuhamel f a x)
      (heatDuhamel (fun s => euclideanLaplacian (f s)) t x + f t x) t := by
  have hdf (s : ℝ) : ContDiff ℝ 1 (fderiv ℝ (f s)) :=
    (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) (f s) from hf s)).2.2
  have hdm := spatial_fderiv_stronglyMeasurable hfm
    (fun s => (hf s).differentiable (by norm_num))
  have hddm := spatial_fderiv_stronglyMeasurable hdm
    (fun s => (hdf s).differentiable (by norm_num))
  have htrace : StronglyMeasurable
      (fun p : ℝ × V => euclideanLaplacian (f p.1) p.2) := by
    let tr (A : V →L[ℝ] V →L[ℝ] F) :=
      ∑ i : Fin (n + 1), A (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))
    have htr : Continuous tr := by dsimp [tr]; fun_prop
    exact htr.comp_stronglyMeasurable hddm
  let H (a s : ℝ) := heatAverage (a - s) (f s) x
  let A (s : ℝ) := heatAverage (t - s) (euclideanLaplacian (f s)) x
  let K := Real.toNNReal ((n + 1) * E)
  have hm (a : ℝ) : StronglyMeasurable (H a) := heatAverage_time_stronglyMeasurable hfm a x
  have hi (a b c : ℝ) : IntervalIntegrable (H a) volume b c := by
    let : IsFiniteMeasure ((volume : Measure ℝ).restrict (uIoc b c)) := by
      unfold uIoc
      infer_instance
    rw [intervalIntegrable_iff]
    exact (integrable_const C).mono' (hm a).aestronglyMeasurable
      (Eventually.of_forall (fun s => heatAverage_norm_le (hf s).continuous (hb s) (a - s) x))
  have hAm : StronglyMeasurable A := heatAverage_time_stronglyMeasurable htrace t x
  have hheat (s : ℝ) : LipschitzWith K (fun a => heatAverage a (f s) x) :=
    heatAverage_time_lipschitz (hf s).continuous ((hf s).continuous_fderiv (by norm_num))
      ((hdf s).continuous_fderiv (by norm_num))
      (fun y => ((hf s).differentiable (by norm_num) y).hasFDerivAt)
      (fun y => ((hdf s).differentiable (by norm_num) y).hasFDerivAt)
      (hb s) (hdb s) (hddb s) x
  have hL (s : ℝ) : LipschitzWith K (fun a => H a s) := by
    apply LipschitzWith.of_dist_le_mul
    intro a c
    calc
      _ ≤ (K : ℝ) * dist (a - s) (c - s) := (hheat s).dist_le_mul (a - s) (c - s)
      _ = _ := by congr 1; simp only [Real.dist_eq]; congr 1; ring
  have hd (s : ℝ) (hs : s ∈ Ico 0 t) : HasDerivAt (fun a => H a s) (A s) t := by
    have h := heatAverage_hasDerivAt_trace (hf s).continuous
      ((hf s).continuous_fderiv (by norm_num)) ((hdf s).continuous_fderiv (by norm_num))
      (fun y => ((hf s).differentiable (by norm_num) y).hasFDerivAt)
      (fun y => ((hdf s).differentiable (by norm_num) y).hasFDerivAt)
      (hb s) (hdb s) (hddb s) (sub_pos.mpr hs.2) x
    change HasDerivAt (fun a => heatAverage (a - s) (f s) x)
      (heatAverage (t - s) (fun y => ∑ i : Fin (n + 1),
        fderiv ℝ (fderiv ℝ (f s)) y (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ))) x) t
    simpa only [Function.comp_def, one_smul, id_eq] using
      h.scomp t ((hasDerivAt_id t).sub_const s)
  have hgap (s : ℝ) : ‖H t s - f s x‖ ≤ (K : ℝ) * |s - t| := by
    simpa only [H, heatAverage_zero, dist_eq_norm, sub_zero, Real.norm_eq_abs,
      abs_sub_comm] using (hheat s).dist_le_mul (t - s) 0
  have hgaplim : Tendsto (fun s => H t s - f s x) (𝓝 t) (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [dist_zero_right]
    have hz : Tendsto (fun s : ℝ => (K : ℝ) * |s - t|) (𝓝 t) (𝓝 0) := by
      simpa using (((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 t) (𝓝 t)).sub_const t).abs.const_mul
        (K : ℝ))
    exact squeeze_zero (fun s => norm_nonneg _) hgap hz
  have hc : ContinuousAt (H t) t := by
    change Tendsto (H t) (𝓝 t) (𝓝 (H t t))
    simpa only [sub_add_cancel, zero_add, H, sub_self, heatAverage_zero] using
      hgaplim.add htime.tendsto
  simpa only [H, A, heatDuhamel, sub_self, heatAverage_zero] using
    moving_time_integral_hasDerivAt ht hm hi hAm hL hd hc

end PoincareConjecture.M35.RadialGauge
