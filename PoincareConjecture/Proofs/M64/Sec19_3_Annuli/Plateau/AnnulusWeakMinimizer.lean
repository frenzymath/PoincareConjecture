import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMinimizerExistence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusEnergyIdentity

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

theorem m64Annulus_exists_weak_energy_minimizer
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A0 : M64Annulus g c0 c1) :
    ∃ (m : ℕ) (e : M → EuclideanSpace ℝ (Fin m))
      (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (L : M64ObservedWeakAnnulus (n := n) e c0 c1),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧ Continuous B ∧
      (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
      (∀ (q : M) (v : TangentSpace (𝓡 n) q),
        B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v) ∧
      (∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, L.energy B ≤ W.energy B) ∧
      ∀ A : M64Annulus g c0 c1,
        L.energy B ≤ ∫ p in interior m64AnnulusDomain, m60EnergyDensity g A.map p := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨W0, -, -⟩ := m64ObservedWeakAnnulus_of_annulus A0 e he1
  obtain ⟨B, L, hB, hpos, hsymm, hgram, hL⟩ :=
    m64ObservedWeakAnnulus_exists_minimizer g e he1 hei hread W0
  have hdiag (q : M) (v : TangentSpace (𝓡 n) q) :
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v :=
    m64ObservedMetric_tangent_diagonal g e he1 B hgram q v
  refine ⟨m, e, B, L, he, hei, hread, hB, hpos, hsymm, hdiag, hL, ?_⟩
  intro A
  obtain ⟨W, -, henergy⟩ := m64ObservedWeakAnnulus_exists_seed_with_energy A e he1 B hdiag
  exact (hL W).trans_eq henergy

theorem M64Annulus.energy_integrable
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) :
    IntegrableOn (m60EnergyDensity g A.map) m64AnnulusDomain volume := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨B, K, hB, -, hb, -, -, hgram⟩ := m64ChartReadable_observed_metric g e he1 hread
  obtain ⟨W, hmap, hcol⟩ := m64ObservedWeakAnnulus_of_annulus A e he1
  have hdiag := m64ObservedMetric_tangent_diagonal g e he1 B hgram
  have hae := m64ObservedWeakAnnulus_seed_energyDensity_eq_ae A e he1 B hdiag W hmap hcol
  change Integrable _ (volume.restrict m64AnnulusDomain)
  rw [m64Annulus_restrict_closed_eq_interior]
  exact (W.energy_integrable B hB hei.isEmbedding hb).congr hae

end PoincareConjecture
