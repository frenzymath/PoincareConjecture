import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.SublevelVolume.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Singleton









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace Poincare.Analysis

private theorem tendsto_of_eventually_quadratic_distortion
    {X : Type*} {l : Filter X} {F : X → ℝ} {L : ℝ}
    (h : ∀ K : ℝ≥0, 1 < K → ∀ᶠ x in l,
      L / (K : ℝ) ^ 2 ≤ F x ∧ F x ≤ (K : ℝ) ^ 2 * L) :
    Tendsto F l (𝓝 L) := by
  have hlc : ContinuousAt (fun K : ℝ≥0 => L / (K : ℝ) ^ 2) 1 :=
    continuousAt_const.div (NNReal.continuous_coe.continuousAt.pow 2) (by norm_num)
  have huc : ContinuousAt (fun K : ℝ≥0 => (K : ℝ) ^ 2 * L) 1 := by fun_prop
  have hl : Tendsto (fun K : ℝ≥0 => L / (K : ℝ) ^ 2) (𝓝[>] 1) (𝓝 L) := by
    simpa using hlc.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun K : ℝ≥0 => (K : ℝ) ^ 2 * L) (𝓝[>] 1) (𝓝 L) := by
    simpa using huc.tendsto.mono_left nhdsWithin_le_nhds
  have hright : ∀ᶠ K : ℝ≥0 in 𝓝[>] 1, 1 < K := self_mem_nhdsWithin
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨K, hK, hcK⟩ := (hright.and (hl.eventually (lt_mem_nhds hc))).exists
    filter_upwards [h K hK] with x hx
    exact hcK.trans_le hx.1
  · intro c hc
    obtain ⟨K, hK, hKc⟩ := (hright.and (hu.eventually (gt_mem_nhds hc))).exists
    filter_upwards [h K hK] with x hx
    exact hx.2.trans_lt hKc

end Poincare.Analysis

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [CompactSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}



theorem tendsto_sublevelVolume_div_sub_min (D : LeviCivitaData g)
    {f : S → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) {p : S}
    (hmin : ∀ x, f p ≤ f x) (huniq : ∀ x, f x = f p → x = p)
    (hgrad : D.gradient f p = 0) {a : ℝ} (ha : 0 < a)
    (hhess : ∀ v w, D.hessian f p v w = a * g.inner p v w) :
    Tendsto (fun t : ℝ => (g.volumeMeasure (f ⁻¹' Ioo (f p) t)).toReal / (t - f p))
      (𝓝[>] f p) (𝓝 (2 * Real.pi / a)) := by
  obtain ⟨e, he0, hep, he, hei, hefs, hdf, hess, hρ⟩ :=
    D.exists_sublevel_normal_chart hf hgrad hhess
  have hbound : ∀ K : ℝ≥0, 1 < K → ∀ᶠ t in 𝓝[>] f p,
      (2 * Real.pi / a) / (K : ℝ) ^ 2 ≤
          (g.volumeMeasure {x | f x < t}).toReal / (t - f p) ∧
        (g.volumeMeasure {x | f x < t}).toReal / (t - f p) ≤
          (K : ℝ) ^ 2 * (2 * Real.pi / a) := by
    intro K hK
    simpa only [hep] using g.eventually_sublevel_volume_ratio_bounds e he0 he hei hf.continuous
      hefs hdf ha hess hρ (by simpa only [hep] using hmin)
      (by simpa only [hep] using huniq) hK
  have hlimit := Poincare.Analysis.tendsto_of_eventually_quadratic_distortion hbound
  let : NullSingletonClass g.volumeMeasure := g.volumeMeasure_nullSingletonClass (by norm_num)
  have hsets (t : ℝ) : f ⁻¹' Ioo (f p) t = {x | f x < t} \ {p} := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.2, ?_⟩
      intro hxp
      have hxp' : x = p := hxp
      simpa only [hxp', lt_self_iff_false] using hx.1
    · rintro ⟨hxt, hxp⟩
      exact ⟨lt_of_le_of_ne (hmin x) (fun heq => hxp (huniq x heq.symm)), hxt⟩
  convert hlimit using 1
  funext t
  rw [hsets, measure_sdiff_null (measure_singleton p)]

end PoincareConjecture.LeviCivitaData
