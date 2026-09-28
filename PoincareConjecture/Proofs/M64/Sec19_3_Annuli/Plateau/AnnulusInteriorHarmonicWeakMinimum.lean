import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizerHarmonicCharts









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak CoordinateExponential ConnectionVariation
  ConjugateVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}



theorem m64Annulus_exists_interior_harmonic_weak_energy_minimizer
    [CompactSpace M] (A0 : M64Annulus g c0 c1) :
    ∃ (m : ℕ) (e : M → EuclideanSpace ℝ (Fin m))
      (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (A : M64ObservedWeakAnnulus (n := n) e c0 c1),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧ Continuous Q ∧
      (∀ q v, 0 ≤ Q q v v) ∧ (∀ q v w, Q q v w = Q q w v) ∧
      (∀ (q : M) (v : TangentSpace (𝓡 n) q),
        Q q (mfderiv (𝓡 n) (𝓡 m) e q v)
          (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v) ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map (interior m64AnnulusDomain) ∧
      (∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) ∧
      (∀ B : M64Annulus g c0 c1,
        A.energy Q ≤ ∫ p in interior m64AnnulusDomain,
          m60EnergyDensity g B.map p) ∧
      ∀ a ∈ interior m64AnnulusDomain,
        ∃ (b : M) (u : LoopPlane → EuclideanSpace ℝ (Fin n)) (R : ℝ),
          0 < R ∧ Metric.closedBall a R ⊆ interior m64AnnulusDomain ∧
          ContDiffOn ℝ ∞ u (Metric.ball a R) ∧
          MapsTo u (Metric.closedBall a R) (extChartAt (𝓡 n) b).target ∧
          EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map
            (Metric.closedBall a R) ∧
          ∀ p ∈ Metric.ball a R, (∑ i : Fin 2,
            covDerivAlong
              (christoffelBilinear
                (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)) u
              (fun q => fderiv ℝ u q (EuclideanSpace.basisFun (Fin 2) ℝ i))
              (EuclideanSpace.basisFun (Fin 2) ℝ i) p) = 0 := by
  obtain ⟨m, e, Q, A, he, hei, hread, hQ, hpos, hsymm, hdiag, hA, hmin, hbound⟩ :=
    m64Annulus_exists_interior_smooth_weak_energy_minimizer A0
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  have hb : ∀ q, ‖Q q‖ ≤ C := fun q => hC _ (mem_range_self q)
  refine ⟨m, e, Q, A, he, hei, hread, hQ, hpos, hsymm, hdiag, hA, hmin, hbound, ?_⟩
  intro a ha
  exact A.exists_harmonic_chart_of_energy_minimum g (he.of_le (by norm_num))
    hei.isEmbedding hread Q hQ hb hdiag hmin hA.continuousOn ha

end PoincareConjecture
