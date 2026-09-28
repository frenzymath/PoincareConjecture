import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Components
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Noncollapse








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



theorem exists_subsequence_ball_volume_lower_bound_of_frequently
    {n : ℕ} (hn : 1 ≤ n) (C : ℕ → FlowCarrier.{u} n)
    (g : ∀ k, RiemannianMetric n (C k).carrier)
    (D : ∀ k, LeviCivitaData (g k))
    (hcomplete : ∀ᶠ k in atTop, MetricComplete (g k))
    (hRic : ∀ᶠ k in atTop, ∀ x : (C k).carrier, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (D k).ricci x v v)
    (p : ∀ k, (C k).carrier) {ν : ℝ} (hν : 0 ≤ ν)
    (hfailure : ∀ R : ℝ, 0 < R → ∃ᶠ k in atTop,
      ENNReal.ofReal (ν * R ^ n) ≤ (g k).volumeMeasure ((g k).ball (p k) R)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (ν * r ^ n) ≤
        (g (σ k)).volumeMeasure ((g (σ k)).ball (p (σ k)) r) := by
  obtain ⟨σ, hσ, hvolume⟩ := extraction_forall_of_frequently
    (fun j : ℕ => ((hfailure ((j : ℝ) + 1) (by positivity)).and_eventually
      hcomplete).and_eventually hRic)
  refine ⟨σ, hσ, ?_⟩
  intro r hr
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop r] with k hk
  have hR : 0 < (k : ℝ) + 1 := by positivity
  have hbig : ν ≤
      ((g (σ k)).volumeMeasure ((g (σ k)).ball (p (σ k)) ((k : ℝ) + 1))).toReal /
        ((k : ℝ) + 1) ^ n := by
    apply (le_div_iff₀ (pow_pos hR n)).mpr
    have h := ENNReal.toReal_mono
      ((g (σ k)).ball_volume_ne_top_of_metricComplete (hvolume k).1.2 _ _)
      (hvolume k).1.1
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hν (pow_nonneg hR.le n))] using h
  have hratio := (g (σ k)).antitoneOn_ball_volume_div_pow (D (σ k)) hn
    (hvolume k).1.2 (hvolume k).2 (p (σ k)) hr hR (by linarith : r ≤ (k : ℝ) + 1)
  have hsmall := (le_div_iff₀ (pow_pos hr n)).mp (hbig.trans hratio)
  exact (ENNReal.ofReal_le_ofReal hsmall).trans_eq
    (ENNReal.ofReal_toReal
      ((g (σ k)).ball_volume_ne_top_of_metricComplete (hvolume k).1.2 _ _))

end PoincareConjecture.RiemannianMetric
