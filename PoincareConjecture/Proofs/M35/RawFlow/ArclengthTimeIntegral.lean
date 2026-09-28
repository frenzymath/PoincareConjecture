import PoincareConjecture.Proofs.M35.RawFlow.AxisTimeCoefficients
import Mathlib.Analysis.Calculus.ParametricIntegral









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)



theorem raw_radialArclength_hasDerivAt_integral {t : ℝ} (ht : t ∈ Ioo 0 G.lifetime)
    {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun s => radialArclength (G.flow.metric s) r)
      (∫ a in (0 : ℝ)..r, rawAxisSpeedTimeDerivative G t a) t := by
  have ht0 : 0 < t := ht.1
  have htL : t < G.lifetime := ht.2
  let d := min t (G.lifetime - t) / 2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdt : d < t := by
    dsimp only [d]
    linarith [min_le_left t (G.lifetime - t)]
  have hdL : d < G.lifetime - t := by
    dsimp only [d]
    linarith [min_le_right t (G.lifetime - t)]
  have hvalid {s : ℝ} (hs : s ∈ Icc (t - d) (t + d)) : s ∈ Ioo 0 G.lifetime := by
    constructor <;> linarith [hs.1, hs.2]
  have hc (s : ℝ) : Continuous (fun a => axisRadialSpeed (G.flow.metric s) a) :=
    (axisRadialCoefficient_contDiff (G.flow.metric s)).continuous.sqrt
  have hdc (s : ℝ) (hs : s ∈ Ico 0 G.lifetime) :
      Continuous (rawAxisSpeedTimeDerivative G s) := by
    rw [← continuousOn_univ]
    have hm : MapsTo (fun a : ℝ => (s, a)) univ (Ico 0 G.lifetime ×ˢ univ) :=
      fun _ _ => ⟨hs, mem_univ _⟩
    have hc' : Continuous (fun a : ℝ => (s, a)) := continuous_const.prodMk continuous_id
    have hh := (rawAxisSpeedTimeDerivative_contDiffOn G).continuousOn.comp hc'.continuousOn hm
    exact hh
  have hcompact := (isCompact_Icc : IsCompact (Icc (t - d) (t + d))).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) r))
  have hdp : ContinuousOn (Function.uncurry (rawAxisSpeedTimeDerivative G))
      (Icc (t - d) (t + d) ×ˢ Icc 0 r) :=
    (rawAxisSpeedTimeDerivative_contDiffOn G).continuousOn.mono
      (fun p hp => ⟨⟨(hvalid hp.1).1.le, (hvalid hp.1).2⟩, mem_univ _⟩)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hdp
  have hs : Ioo (t - d) (t + d) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) r))
    (F := fun s a => axisRadialSpeed (G.flow.metric s) a)
    (F' := rawAxisSpeedTimeDerivative G) (bound := fun _ => C) hs
    (Filter.Eventually.of_forall (fun s => (hc s).aestronglyMeasurable))
    ((hc t).integrableOn_Ioc)
    ((hdc t ⟨ht.1.le, ht.2⟩).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [] with a ha s hs'
      exact hC (s, a) ⟨⟨hs'.1.le, hs'.2.le⟩, ⟨ha.1.le, ha.2⟩⟩)
    (integrable_const C)
    (by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [] with a _ s hs'
      have hst := hvalid ⟨hs'.1.le, hs'.2.le⟩
      exact (raw_axisRadialSpeed_hasDerivWithinAt G ⟨hst.1.le, hst.2⟩ a).hasDerivAt
        (mem_of_superset (Ioo_mem_nhds hst.1 hst.2) Ioo_subset_Ico_self))
  simpa only [radialArclength, axisRadialSpeed, intervalIntegral.integral_of_le hr] using h.2

end PoincareConjecture.M35.Uniqueness
