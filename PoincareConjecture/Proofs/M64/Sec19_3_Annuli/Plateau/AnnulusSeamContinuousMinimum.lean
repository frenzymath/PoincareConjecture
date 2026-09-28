import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizer












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]



theorem m64Annulus_exists_seam_continuous_weak_energy_minimizer
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A0 : M64Annulus g c0 c1) :
    ∃ (m : ℕ) (e : M → EuclideanSpace ℝ (Fin m))
      (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (A : M64ObservedWeakAnnulus (n := n) e c0 c1),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧ Continuous Q ∧
      (∀ q w, 0 ≤ Q q w w) ∧ (∀ q w z, Q q w z = Q q z w) ∧
      (∀ (q : M) (w : TangentSpace (𝓡 n) q),
        Q q (mfderiv (𝓡 n) (𝓡 m) e q w) (mfderiv (𝓡 n) (𝓡 m) e q w) = g.inner q w w) ∧
      ContinuousOn A.map m64AnnulusSeamDomain ∧
      (∀ p ∈ m64AnnulusSeamLeft, A.map (m64AnnulusSeamTranslation + p) = A.map p) ∧
      (∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) ∧
      ∀ B : M64Annulus g c0 c1,
        A.energy Q ≤ ∫ p in interior m64AnnulusDomain, m60EnergyDensity g B.map p := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨W0, -, -⟩ := m64ObservedWeakAnnulus_of_annulus A0 e he1
  obtain ⟨Q, W, hQ, hpos, hsymm, hgram, hW⟩ :=
    m64ObservedWeakAnnulus_exists_minimizer g e he1 hei hread W0
  obtain ⟨C, hC, hcoercive⟩ := m64ObservedMetric_tangent_coercivity g e he1 Q hgram
  obtain ⟨A, hAcont, -, -, hshift, -, -, hA⟩ :=
    W.seam_continuous_representative g he1 hei hread Q hQ hpos hC hcoercive hW
  have hdiag := m64ObservedMetric_tangent_diagonal g e he1 Q hgram
  refine ⟨m, e, Q, A, he, hei, hread, hQ, hpos, hsymm, hdiag, hAcont, hshift, hA, ?_⟩
  intro B
  obtain ⟨V, -, henergy⟩ := m64ObservedWeakAnnulus_exists_seed_with_energy B e he1 Q hdiag
  exact (hA V).trans_eq henergy

end PoincareConjecture
