import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizer

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

theorem m64Annulus_exists_continuous_modulus_minimizer
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A0 : M64Annulus g c0 c1)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ (m : ℕ) (e : M → EuclideanSpace ℝ (Fin m))
      (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (r : ℝ) (L : M64ObservedWeakAnnulus (n := n) e c0 c1),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧ Continuous B ∧
      (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
      (∀ (q : M) (v : TangentSpace (𝓡 n) q),
        B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v) ∧
      r ∈ Icc lo hi ∧ ContinuousOn L.map (interior m64AnnulusDomain) ∧
      ∀ s ∈ Icc lo hi, ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
        L.weightedEnergy B r ≤ W.weightedEnergy B s := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨W0, -, -⟩ := m64ObservedWeakAnnulus_of_annulus A0 e he1
  obtain ⟨B, r, hr, L, hB, hpos, hsymm, hgram, hLcont, hmin⟩ :=
    m64ObservedWeakAnnulus_exists_continuous_modulus_minimizer
      g e he1 hei hread hlo hlohi W0
  exact ⟨m, e, B, r, L, he, hei, hread, hB, hpos, hsymm,
    m64ObservedMetric_tangent_diagonal g e he1 B hgram, hr, hLcont, hmin⟩

end PoincareConjecture
