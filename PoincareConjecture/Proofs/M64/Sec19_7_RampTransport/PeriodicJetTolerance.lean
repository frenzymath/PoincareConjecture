import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import Mathlib.Topology.UniformSpace.HeineCantor













set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff

namespace PoincareConjecture.M64.RampTransport




theorem exists_periodic_jet_scalar_tolerance
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {O : Set (W × W × W)} (hO : IsOpen O) {f : W × W × W → ℝ}
    (hf : ContinuousOn f O) {period : ℝ} (hperiod : 0 < period)
    {c : ℝ → W} (hc : ContDiff ℝ 2 c) (hp : Function.Periodic c period)
    (hjet : ∀ x, (c x, deriv c x, deriv (deriv c) x) ∈ O)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ r : ℝ → W,
      (∀ x, ‖r x - c x‖ < delta ∧ ‖deriv r x - deriv c x‖ < delta ∧
        ‖deriv (deriv r) x - deriv (deriv c) x‖ < delta) →
      ∀ x, |f (r x, deriv r x, deriv (deriv r) x) -
        f (c x, deriv c x, deriv (deriv c) x)| < epsilon := by
  have hc1 : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hp1 := hp.deriv_of_differentiable (hc.differentiable (by norm_num))
  have hp2 := hp1.deriv_of_differentiable (hc1.differentiable (by norm_num))
  let jet := fun x => (c x, deriv c x, deriv (deriv c) x)
  have hjetp : Function.Periodic jet period := by
    intro x
    dsimp only [jet]
    rw [hp x, hp1 x, hp2 x]
  have hjetc : Continuous jet :=
    hc.continuous.prodMk (hc1.continuous.prodMk hc1.continuous_deriv_one)
  have hcompact : IsCompact (range jet) :=
    hjetp.compact_of_continuous hperiod.ne' hjetc
  have hlocal : ∀ z ∈ range jet, ContinuousAt f z := by
    rintro _ ⟨x, rfl⟩
    exact hf.continuousAt (hO.mem_nhds (hjet x))
  obtain ⟨delta, hdelta, hnear⟩ := Metric.mem_uniformity_dist.mp
    (hcompact.uniformContinuousAt_of_continuousAt f hlocal
      (Metric.dist_mem_uniformity hepsilon))
  refine ⟨delta, hdelta, ?_⟩
  intro r hr x
  have hdist : dist (jet x) (r x, deriv r x, deriv (deriv r) x) < delta := by
    rw [dist_eq_norm]
    change max ‖c x - r x‖
      (max ‖deriv c x - deriv r x‖ ‖deriv (deriv c) x - deriv (deriv r) x‖) < delta
    rw [norm_sub_rev (c x) (r x), norm_sub_rev (deriv c x) (deriv r x),
      norm_sub_rev (deriv (deriv c) x) (deriv (deriv r) x)]
    exact max_lt (hr x).1 (max_lt (hr x).2.1 (hr x).2.2)
  have h := hnear hdist (mem_range_self x)
  change dist (f (jet x)) (f (r x, deriv r x, deriv (deriv r) x)) < epsilon at h
  simpa only [Real.dist_eq, jet, abs_sub_comm] using h

end PoincareConjecture.M64.RampTransport
