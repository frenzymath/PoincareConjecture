import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskHarmonicChart











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M65StrictTrace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem exists_closedDisk_harmonic_chart (D : LeviCivitaData g)
    {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (Metric.ball (0 : LoopPlane) 1))
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hharm : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    {x : LoopPlane} (hx : x ∈ loopDiskSet) :
    let q := chartAt LoopAmbient (f x)
    let G := q ∘ f
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE) (O : Set LoopPlane),
      IsOpen O ∧ x ∈ O ∧ MapsTo f (loopDiskSet ∩ O) q.source ∧
      ContDiffOn ℝ 1 G (loopDiskSet ∩ O) ∧
      ContDiffOn ℝ ∞ G (Metric.ball (0 : LoopPlane) 1 ∩ O) ∧
      (∀ z ∈ loopDiskSet ∩ O, ∀ᶠ y in 𝓝 (G z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (q.symm y)
          (mfderiv (𝓡 3) (𝓡 3) q.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) q.symm y b)) ∧
      ∀ z ∈ Metric.ball (0 : LoopPlane) 1 ∩ O,
        (∑ i : Fin 2, fderiv ℝ (fderiv ℝ G) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
          ∑ i : Fin 2, M65Gauss.connectionCoefficient DE (G z)
            (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  let q := chartAt LoopAmbient (f x)
  let G := q ∘ f
  obtain ⟨gE, DE, hE⟩ := m65Exists_chartMetric g (f x)
  have hmetric : ∀ᶠ y in 𝓝 (G x), ∀ a b : LoopAmbient,
      gE.inner y a b = g.inner (q.symm y)
        (mfderiv (𝓡 3) (𝓡 3) q.symm y a)
        (mfderiv (𝓡 3) (𝓡 3) q.symm y b) := by
    simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, q, G,
      Function.comp_apply, id_eq] using hE
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hmetric
  have hxsource : f x ∈ q.source := mem_chart_source LoopAmbient (f x)
  have hq : ContMDiffAt (𝓡 3) (𝓡 3) 1 q (f x) :=
    (contMDiffOn_chart (n := 1) _ hxsource).contMDiffAt (q.open_source.mem_nhds hxsource)
  have hGx : ContinuousWithinAt G loopDiskSet x :=
    (hq.comp_contMDiffWithinAt x (hb x hx)).continuousWithinAt
  have hsource : ∀ᶠ z in 𝓝[loopDiskSet] x, f z ∈ q.source :=
    (hb.continuousOn x hx) (q.open_source.mem_nhds hxsource)
  have htarget : ∀ᶠ z in 𝓝[loopDiskSet] x, G z ∈ V := hGx (hVopen.mem_nhds hxV)
  obtain ⟨W, hW, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hsource.and htarget)
  obtain ⟨O, hOW, hOopen, hxO⟩ := mem_nhds_iff.mp hW
  have hall (z : LoopPlane) (hz : z ∈ loopDiskSet ∩ O) : f z ∈ q.source ∧ G z ∈ V :=
    hWsub ⟨hOW hz.2, hz.1⟩
  have hmap : MapsTo f (loopDiskSet ∩ O) q.source := fun z hz => (hall z hz).1
  have hmap' : MapsTo f (Metric.ball (0 : LoopPlane) 1 ∩ O) q.source :=
    fun z hz => hmap ⟨Metric.ball_subset_closedBall hz.1, hz.2⟩
  have hGclosed : ContDiffOn ℝ 1 G (loopDiskSet ∩ O) :=
    (contMDiffOn_chart.comp (hb.mono inter_subset_left) hmap).contDiffOn
  have hGopen : ContDiffOn ℝ ∞ G (Metric.ball (0 : LoopPlane) 1 ∩ O) :=
    (contMDiffOn_chart.comp (hf.mono inter_subset_left) hmap').contDiffOn
  have hmet (z : LoopPlane) (hz : z ∈ loopDiskSet ∩ O) :
      ∀ᶠ y in 𝓝 (G z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (q.symm y)
          (mfderiv (𝓡 3) (𝓡 3) q.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) q.symm y b) :=
    mem_of_superset (hVopen.mem_nhds (hall z hz).2) hVsub
  refine ⟨gE, DE, O, hOopen, hxO, hmap, hGclosed, hGopen, hmet, ?_⟩
  intro z hz
  exact M65Gauss.harmonic_coordinate_equation D DE (f x) Metric.isOpen_ball hf hz.1
    (hmap' hz) (hmet z ⟨Metric.ball_subset_closedBall hz.1, hz.2⟩) (hharm z hz.1)

end PoincareConjecture.M65StrictTrace
