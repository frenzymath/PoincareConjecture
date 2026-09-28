import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.TrimmedIntrinsicMetric
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.InducedMetricComposition
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.SurfaceMetricTransport
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.AnnulusStripGauss





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

open M64Uniformization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}




theorem m64Annulus_trimmed_gaussian_bound
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {eps : ℝ} (hpos : 0 < eps) (hsmall : eps < 1 / 2)
    (N : IntrinsicAnnulus) {F : LoopPlane → M}
    (hdesc : ∀ z : ℝ × ℝ, 0 < z.1 →
      F (scalarCoverMap z) = A.map (m64TrimmedCoverCoordinate eps z))
    (hmetric : ∀ p ∈ standardAnnulusDomain, ∀ᶠ q in 𝓝 p, ∀ u v,
      N.metric.inner q u v = g.inner (F q) (mfderiv (𝓡 2) (𝓡 n) F q u)
        (mfderiv (𝓡 2) (𝓡 n) F q v))
    {K : ℝ} (hsec : ∀ p u v, D.sectionalCurvature p u v ≤ K) :
    N.GaussianCurvatureBound K := by
  have hstrip : ∀ p ∈ m64AnnulusOpenStrip,
      Function.Injective (mfderiv (𝓡 2) (𝓡 n) A.map p) := by
    intro p hp
    have hsub : m64AnnulusOpenStrip ⊆ {q : LoopPlane | q 1 ∈ Icc (0 : ℝ) 1} :=
      fun _ hq => ⟨hq.1.le, hq.2.le⟩
    have hi := M64.annulus_strip_within_injective A hAc hinj p (hsub hp)
    rw [mfderivWithin_of_mem_nhds
      (mem_of_superset (isOpen_m64AnnulusOpenStrip.mem_nhds hp) hsub)] at hi
    exact hi
  intro p hp
  have hpU := standardAnnulusDomain_subset_trimmedNeighborhood hpos hsmall hp
  obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjective_of_ne_zero (norm_pos_iff.mp hpU.1)
  have hzstrip : m64TrimmedCoverCoordinate eps z ∈ m64AnnulusOpenStrip := by
    change eps + (1 - 2 * eps) * (z.1 - 1) ∈ Ioo (0 : ℝ) 1
    simpa only [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos hz] using hpU.2
  obtain ⟨q, hq, hqz, hcomp⟩ := scalarCoverDescent_local_germ hdesc hz
  let k : LoopPlane → LoopPlane := m64TrimmedCoverCoordinate eps ∘ q
  have hk : ContDiffAt ℝ ∞ k (scalarCoverMap z) :=
    (m64TrimmedCoverCoordinate_contDiff eps).contDiffAt.comp _ hq
  have hkp : k (scalarCoverMap z) ∈ m64AnnulusOpenStrip := by
    simpa only [k, Function.comp_apply, hqz] using hzstrip
  obtain ⟨H, DH, hH⟩ := m64_exists_induced_metric_near g isClosed_singleton
    isOpen_m64AnnulusOpenStrip (singleton_subset_iff.mpr hkp) hAi hstrip
  have hHmetric := hH _ (mem_singleton (k (scalarCoverMap z)))
  have hAf : ∀ᶠ x in 𝓝 (k (scalarCoverMap z)),
      MDifferentiableAt (𝓡 2) (𝓡 n) A.map x := by
    filter_upwards [isOpen_m64AnnulusOpenStrip.mem_nhds hkp] with x hx
    exact (hAi.contMDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds hx)).mdifferentiableAt
      (by simp)
  have hmetricComp := m64_induced_metrics_comp_germ g N.metric H
    (hk.of_le (by simp)) hAf hcomp (hmetric _ hp) hHmetric
  change N.connection.scalarCurvature (scalarCoverMap z) / 2 ≤ K
  rw [m64_gaussian_eq_of_induced_surface_germ N.connection DH hk hmetricComp]
  exact m64Annulus_induced_gaussian_le D DH A hr hminimum hconf hAc hAi hinj hkp
    hHmetric (hsec _)

end PoincareConjecture
