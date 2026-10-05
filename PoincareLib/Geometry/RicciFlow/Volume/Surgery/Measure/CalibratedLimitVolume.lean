import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.CalibratedTransport
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Analysis.FatouSum
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Topology.PartialChartMeasurable

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/CalibratedLimitVolume.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Calibrated volume under convergence of actual chart densities

Morgan-Tian Theorem 11.19(1), p. 279, and Lemma 17.12, p. 410.
Fatou's lemma and a countable disjoint chart refinement compare terminal
volume with the lower limit of the preceding volumes. See stage 7 of
the task derivations for the raw event application.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u v w

namespace PoincareMT.SurgeryVolume

variable {n : ℕ} {M : Type u} {N : Type v} {ι : Type w}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {l : Filter ι} [IsCountablyGenerated l] [NeBot l]

/-- Pointwise convergence of actual coordinate densities gives the local
volume inequality of MT Theorem 11.19(1), p. 279, used in Lemma 17.12, p. 410. -/
theorem calibratedVolume_chart_le_liminf
    (g : ι → RiemannianMetric n M) (gT : RiemannianMetric n N)
    (e0 : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (e1 : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    (h0 : ContMDiffOn (𝓡 n) (𝓡 n) 1 e0 e0.source)
    (h0i : ContMDiffOn (𝓡 n) (𝓡 n) 1 e0.symm e0.target)
    (h1 : ContMDiffOn (𝓡 n) (𝓡 n) 1 e1 e1.source)
    (h1i : ContMDiffOn (𝓡 n) (𝓡 n) 1 e1.symm e1.target)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : MeasurableSet C)
    (hC0 : C ⊆ e0.source) (hC1 : C ⊆ e1.source)
    (hlim : ∀ x ∈ C, Tendsto (fun t => SurgeryVolume.Measure.pullbackJacobian (g t) e0 x) l
      (𝓝 (SurgeryVolume.Measure.pullbackJacobian gT e1 x))) :
    calibratedMetricVolume gT (e1 '' C) ≤
      liminf (fun t => calibratedMetricVolume (g t) (e0 '' C)) l := by
  have hm (t : ι) : AEMeasurable
      (fun x => ENNReal.ofReal (SurgeryVolume.Measure.pullbackJacobian (g t) e0 x)) (volume.restrict C) := by
    apply ContinuousOn.aemeasurable _ hC
    intro x hx
    exact (ENNReal.continuous_ofReal.continuousAt.comp
      (SurgeryVolume.Measure.pullbackJacobian_continuousAt (g t)
        (h0.contMDiffAt (e0.open_source.mem_nhds (hC0 hx))))).continuousWithinAt
  rw [SurgeryVolume.Measure.calibratedMetricVolume_image_eq_lintegral gT e1 h1 h1i hC hC1]
  calc
    _ = ∫⁻ x in C, liminf (fun t => ENNReal.ofReal (SurgeryVolume.Measure.pullbackJacobian (g t) e0 x)) l := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hC] with x hx
      exact (ENNReal.tendsto_ofReal (hlim x hx)).liminf_eq.symm
    _ ≤ liminf (fun t => ∫⁻ x in C,
        ENNReal.ofReal (SurgeryVolume.Measure.pullbackJacobian (g t) e0 x)) l := lintegral_liminf_le' hm
    _ = _ := by
      congr 1
      funext t
      exact (SurgeryVolume.Measure.calibratedMetricVolume_image_eq_lintegral (g t) e0 h0 h0i hC hC0).symm

/-- Disjoint corresponding chart pieces give the global regular-limit
volume inequality of MT Theorem 11.19(1), p. 279, and Lemma 17.12, p. 410. -/
theorem calibratedVolume_le_liminf_of_chart_cover
    (g : ι → RiemannianMetric n M) (gT : RiemannianMetric n N)
    (e0 : ℕ → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (e1 : ℕ → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    (h0 : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) 1 (e0 k) (e0 k).source)
    (h0i : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) 1 (e0 k).symm (e0 k).target)
    (h1 : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) 1 (e1 k) (e1 k).source)
    (h1i : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) 1 (e1 k).symm (e1 k).target)
    (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hC : ∀ k, MeasurableSet (C k))
    (hC0 : ∀ k, C k ⊆ (e0 k).source) (hC1 : ∀ k, C k ⊆ (e1 k).source)
    (hdis0 : Pairwise (fun i j => Disjoint (e0 i '' C i) (e0 j '' C j)))
    (hdis1 : Pairwise (fun i j => Disjoint (e1 i '' C i) (e1 j '' C j)))
    (hcover : ⋃ k, e1 k '' C k = univ)
    (hlim : ∀ k, ∀ x ∈ C k, Tendsto (fun t => SurgeryVolume.Measure.pullbackJacobian (g t) (e0 k) x) l
      (𝓝 (SurgeryVolume.Measure.pullbackJacobian gT (e1 k) x))) :
    calibratedMetricVolume gT univ ≤ liminf (fun t => calibratedMetricVolume (g t) univ) l := by
  have hm0 (k : ℕ) := (e0 k).measurableSet_image_of_subset_source (hC k) (hC0 k)
  have hm1 (k : ℕ) := (e1 k).measurableSet_image_of_subset_source (hC k) (hC1 k)
  calc
    _ = ∑' k, calibratedMetricVolume gT (e1 k '' C k) := by
      rw [← hcover, measure_iUnion hdis1 hm1]
    _ ≤ ∑' k, liminf (fun t => calibratedMetricVolume (g t) (e0 k '' C k)) l :=
      ENNReal.tsum_le_tsum fun k => calibratedVolume_chart_le_liminf g gT (e0 k) (e1 k)
        (h0 k) (h0i k) (h1 k) (h1i k) (hC k) (hC0 k) (hC1 k) (hlim k)
    _ ≤ liminf (fun t => ∑' k, calibratedMetricVolume (g t) (e0 k '' C k)) l :=
      ENNReal.tsum_liminf_le _
    _ ≤ _ := by
      exact Filter.liminf_le_liminf (Eventually.of_forall fun t => tsum_measure_le_measure_univ
        (fun k => (hm0 k).nullMeasurableSet) (fun _ _ h => (hdis0 h).aedisjoint))

end PoincareMT.SurgeryVolume
