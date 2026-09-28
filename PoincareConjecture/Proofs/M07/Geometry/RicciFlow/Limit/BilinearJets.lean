import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Smooth
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LinearPostcompose










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open scoped Manifold ContDiff Bundle Topology
open Filter Set

namespace PoincareConjecture.RicciFlow



theorem exists_of_bilinear_spacetime_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M)
    (hJ : IsOpen J) (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hjets : ∀ (x : M) (r : ℕ)
      (K : Set (ℝ × EuclideanSpace ℝ (Fin n))), IsCompact K →
      K ⊆ J ×ˢ (extChartAt (𝓡 n) x).target →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2))
        (iteratedFDeriv ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            (g p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2)) atTop K) :
    ∃ F : RicciFlow n M J, F.metric = g := by
  apply exists_of_smooth_limit Fseq g hJ hg
  intro x r a b K hK hKU
  let U := J ×ˢ (extChartAt (𝓡 n) x).target
  have hU : IsOpen U := hJ.prod (isOpen_extChartAt_target x)
  have hsmooth (G : ℝ → RiemannianMetric n M)
      (hG : RiemannianMetric.IsSmoothFamilyOn G J) :
      ContDiffOn ℝ ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (G p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2) U := by
    intro p hp
    exact (hG.contDiffAt_spacetime_pullbackCoefficients hJ
      ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hp.2).contMDiffAt
        (extChartAt_target_mem_nhds' hp.2)) hp.1).contDiffWithinAt
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ b)).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ a))
  have h := Poincare.Analysis.Calculus.smooth_convergence_continuousLinearMap_comp
    L hU (hsmooth g hg)
    (fun p hp => ⟨U, hU, hp,
      Eventually.of_forall (fun k => hsmooth (Fseq k).metric (Fseq k).smooth)⟩)
    (hjets x)
  exact h.2 r K hK hKU

end PoincareConjecture.RicciFlow
