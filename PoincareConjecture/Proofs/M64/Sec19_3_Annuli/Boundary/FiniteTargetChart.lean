import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ChartMetricRealization
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem exists_finite_target_chart (g : RiemannianMetric n M)
    {f : E → M} {K W : Set E} (hWK : W ⊆ K)
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) 1 f K)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ f W) {x : E} (hx : x ∈ K) :
    let q := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
    let H := q ∘ f
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_DE : LeviCivitaData gE) (O : Set E),
      IsOpen O ∧ x ∈ O ∧ MapsTo f (K ∩ O) q.source ∧
      ContDiffOn ℝ 1 H (K ∩ O) ∧ ContDiffOn ℝ ∞ H (W ∩ O) ∧
      ∀ z ∈ K ∩ O, gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm := by
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  let H := q ∘ f
  obtain ⟨gE, DE, hE⟩ := m65Exists_chartMetric g (f x)
  have hmetric : gE.euclideanCoefficients =ᶠ[𝓝 (H x)] g.pullbackCoefficients q.symm := by
    have hE' : ∀ᶠ y in 𝓝 (H x), ∀ a b : EuclideanSpace ℝ (Fin n),
        gE.inner y a b = g.inner (q.symm y)
          (mfderiv (𝓡 n) (𝓡 n) q.symm y a) (mfderiv (𝓡 n) (𝓡 n) q.symm y b) := by
      simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
        q, H, Function.comp_apply, id_eq] using hE
    filter_upwards [hE'] with y hy
    ext a b
    exact hy a b
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hmetric
  have hsrc : f x ∈ q.source := mem_chart_source _ _
  have hq : ContMDiffAt (𝓡 n) (𝓡 n) 1 q (f x) :=
    (contMDiffOn_chart (n := 1) _ hsrc).contMDiffAt (q.open_source.mem_nhds hsrc)
  have hHx : ContinuousWithinAt H K x :=
    (hq.comp_contMDiffWithinAt x (hf x hx)).continuousWithinAt
  have hsource : ∀ᶠ z in 𝓝[K] x, f z ∈ q.source :=
    (hf.continuousOn x hx) (q.open_source.mem_nhds hsrc)
  have htarget : ∀ᶠ z in 𝓝[K] x, H z ∈ V := hHx (hVopen.mem_nhds hxV)
  obtain ⟨T, hT, hTsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hsource.and htarget)
  obtain ⟨O, hOT, hO, hxO⟩ := mem_nhds_iff.mp hT
  have hall (z : E) (hz : z ∈ K ∩ O) : f z ∈ q.source ∧ H z ∈ V :=
    hTsub ⟨hOT hz.2, hz.1⟩
  have hmap : MapsTo f (K ∩ O) q.source := fun z hz => (hall z hz).1
  have hmapW : MapsTo f (W ∩ O) q.source := fun z hz => hmap ⟨hWK hz.1, hz.2⟩
  refine ⟨gE, DE, O, hO, hxO, hmap,
    (contMDiffOn_chart.comp (hf.mono inter_subset_left) hmap).contDiffOn,
    (contMDiffOn_chart.comp (hi.mono inter_subset_left) hmapW).contDiffOn, ?_⟩
  intro z hz
  exact mem_of_superset (hVopen.mem_nhds (hall z hz).2) hVsub

end PoincareConjecture.M64
