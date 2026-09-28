import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DensityDomination
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.DiskMetricTransport
import Mathlib.Analysis.Calculus.ParametricIntegral










set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {K0 K1 K2 : ℝ}




theorem m65Disk_metric_variation
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2) (hK2 : 0 ≤ K2)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk (F.metric a) gamma)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    IntegrableOn (m65PlaneRicciTraceDensity (F.connection t) D.map) loopDiskSet volume ∧
      HasDerivAt (fun s => parametrizedRiemannianArea (F.metric s) D.map)
        (-(∫ z in loopDiskSet, m65PlaneRicciTraceDensity (F.connection t) D.map z)) t := by
  let C := (2 * K2) * (Real.exp ((2 * K2) * (b - a))) ^ 2
  let j := fun s z => m60AreaDensity (F.metric s) D.map z
  let bound := fun z => C * j a z
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) hK2) (sq_nonneg _)
  have hbound (z : LoopPlane) : 0 ≤ bound z := mul_nonneg hC (Real.sqrt_nonneg _)
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.le.trans ht.2.le⟩
  have hmeas (s : ℝ) : AEStronglyMeasurable (j s) (volume.restrict loopDiskSet) :=
    m65AreaDensity_aestronglyMeasurable (F.metric s)
      (isCompact_closedBall (0 : LoopPlane) 1) D.continuous_on_disk
      D.ae_manifold_differentiable
  have htrace := m65PlaneRicciTraceDensity_aestronglyMeasurable F
    (isCompact_closedBall (0 : LoopPlane) 1) D.continuous_on_disk
    D.ae_manifold_differentiable ht
  have hlip (z : LoopPlane) : LipschitzOnWith (Real.nnabs (bound z))
      (fun s => j s z) (Icc a b) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs r hr
    simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg (hbound z)]
    exact m65AreaDensity_time_lipschitz_bound F bounds hK2 D.map z hr hs
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := j) (F' := fun z => -m65PlaneRicciTraceDensity (F.connection t) D.map z)
    (bound := bound) (Icc_mem_nhds ht.1 ht.2) (Eventually.of_forall hmeas)
    (m65Disk_newMetric_integrable bounds ha ⟨ht.1.le, ht.2.le⟩ D)
    htrace.neg (Eventually.of_forall hlip) (D.area_integrable.const_mul C)
    (Eventually.of_forall fun z => m65AreaDensity_metric_hasDerivAt F D.map z
      (by simpa only [interior_Icc] using ht))
  refine ⟨?_, ?_⟩
  · exact h.1.neg.congr (Eventually.of_forall fun z => neg_neg _)
  · simpa only [parametrizedRiemannianArea, j,
      m60AreaDensity_eq_parametrizedAreaDensity, integral_neg] using h.2

end PoincareConjecture
