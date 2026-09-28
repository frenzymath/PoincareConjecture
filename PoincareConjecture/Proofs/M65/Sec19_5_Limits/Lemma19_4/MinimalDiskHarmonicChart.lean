import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskTrace
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.HessianTransport
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ChartMetricRealization










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M65Gauss

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}




theorem harmonic_coordinate_equation
    (D : LeviCivitaData g) (DE : LeviCivitaData gE) (p : M)
    {f : LoopPlane → M} {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f U) {x : LoopPlane} (hx : x ∈ U)
    (hsource : f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hmetric : ∀ᶠ y in 𝓝 ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x)),
      ∀ a b : EuclideanSpace ℝ (Fin n),
        gE.inner y a b = g.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y a)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y b))
    (hharm : m65PlaneTension D f x = 0) :
    let G := (chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f
    (∑ i : Fin 2, fderiv ℝ (fderiv ℝ G) x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
      ∑ i : Fin 2, connectionCoefficient DE (G x)
        (fderiv ℝ G x (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ G x (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  let q := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hi : (mfderiv (𝓡 n) (𝓡 n) q.symm (q (f x))).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).symm.mfderiv (q.map_source hsource), rfl⟩
  have hsum : (∑ i : Fin 2, covariantHessianMap DE (q ∘ f) x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
    apply hi.injective
    rw [map_zero, map_sum]
    calc
      _ = ∑ i : Fin 2, m65PlaneHessian D f x
          (EuclideanSpace.basisFun (Fin 2) ℝ i)
          (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (planeHessian_chart D DE p hU hf hx hsource hmetric _ _).symm
      _ = 0 := hharm
  simpa only [covariantHessianMap, Finset.sum_add_distrib, q] using hsum

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {γ : C1FreeLoopSpace (M := M)}





theorem exists_harmonic_chart_neighborhood (S : M65MinimalDisk g connection γ)
    {x : LoopPlane} (hx : x ∈ Metric.ball (0 : LoopPlane) 1) :
    let q := chartAt LoopAmbient (S.disk.map x)
    let G := q ∘ S.disk.map
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE) (W : Set LoopPlane),
      IsOpen W ∧ x ∈ W ∧ W ⊆ Metric.ball (0 : LoopPlane) 1 ∧
      MapsTo S.disk.map W q.source ∧ ContDiffOn ℝ ∞ G W ∧
      (∀ z ∈ W, ∀ u v : LoopAmbient,
        gE.inner (G z) u v = g.inner (q.symm (G z))
          (mfderiv (𝓡 3) (𝓡 3) q.symm (G z) u)
          (mfderiv (𝓡 3) (𝓡 3) q.symm (G z) v)) ∧
      ∀ z ∈ W,
        (∑ i : Fin 2, fderiv ℝ (fderiv ℝ G) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
          ∑ i : Fin 2, M65Gauss.connectionCoefficient DE (G z)
            (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  let q := chartAt LoopAmbient (S.disk.map x)
  let G := q ∘ S.disk.map
  obtain ⟨gE, DE, hE⟩ := m65Exists_chartMetric g (S.disk.map x)
  have hmetric : ∀ᶠ y in 𝓝 (G x), ∀ a b : LoopAmbient,
      gE.inner y a b = g.inner (q.symm y)
        (mfderiv (𝓡 3) (𝓡 3) q.symm y a)
        (mfderiv (𝓡 3) (𝓡 3) q.symm y b) := by
    simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, q, G,
      Function.comp_apply, id_eq] using hE
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hmetric
  let W₀ := Metric.ball (0 : LoopPlane) 1 ∩ S.disk.map ⁻¹' q.source
  have hW₀ : IsOpen W₀ := S.interior_smooth.continuousOn.isOpen_inter_preimage
    Metric.isOpen_ball q.open_source
  have hxW₀ : x ∈ W₀ := ⟨hx, mem_chart_source LoopAmbient (S.disk.map x)⟩
  have hG : ContDiffOn ℝ ∞ G W₀ :=
    (contMDiffOn_chart.comp (S.interior_smooth.mono inter_subset_left)
      (fun _ hz => hz.2)).contDiffOn
  let W := W₀ ∩ G ⁻¹' V
  have hW : IsOpen W := hG.continuousOn.isOpen_inter_preimage hW₀ hVopen
  refine ⟨gE, DE, W, hW, ⟨hxW₀, hxV⟩, fun _ hz => hz.1.1,
    (fun _ hz => hz.1.2), hG.mono inter_subset_left,
    (fun z hz => hVsub hz.2), ?_⟩
  intro z hz
  apply M65Gauss.harmonic_coordinate_equation connection DE (S.disk.map x)
    Metric.isOpen_ball S.interior_smooth hz.1.1 hz.1.2 _ (S.harmonic z hz.1.1)
  exact mem_of_superset (hVopen.mem_nhds hz.2) hVsub

end PoincareConjecture.M65MinimalDisk
