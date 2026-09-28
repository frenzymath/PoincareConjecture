import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.SingularRegularLimit

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option maxHeartbeats 600000 in
private theorem exists_chart_scalar_realization
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (q : M)
    (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ (extChartAt (𝓡 n) q).target) :
    ∃ gd : Σ gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)), LeviCivitaData gE,
      gd.1.euclideanCoefficients =ᶠ[𝓝 p] g.pullbackCoefficients (extChartAt (𝓡 n) q).symm ∧
      gd.2.scalarCurvature p = D.scalarCurvature ((extChartAt (𝓡 n) q).symm p) := by
  let c := extChartAt (𝓡 n) q
  have hpos : ∀ z ∈ c.target, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < g.pullbackCoefficients c.symm z v v := by
    intro z hz v hv
    apply g.pos
    intro hzero
    have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm z).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hz
    apply hv
    apply hi.injective
    rw [map_zero]
    convert! hzero using 1
  obtain ⟨gE, DE, V, hV, hpV, hsub, heq⟩ := RiemannianMetric.exists_local_realization
    (isOpen_extChartAt_target q) hp (g.pullbackCoefficients c.symm)
    (g.contDiffOn_chartCoefficients q) (fun _ _ _ _ => g.symm _ _ _) hpos
  refine ⟨⟨gE, DE⟩, Filter.Eventually.mono (hV.mem_nhds hpV) heq, ?_⟩
  apply DE.scalarCurvature_eq_of_local_isometry D hV
    ((contMDiffOn_extChartAt_symm q).mono hsub) (hx := hpV)
  intro z hz a b
  exact congrArg (fun B => B a b) (heq z hz)

private theorem tendsto_scalar_jets_of_bilinear_jets
    {n : ℕ} {ι : Type w} {l : Filter ι}
    {gseq : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (p a b : EuclideanSpace ℝ (Fin n)) (r : ℕ)
    (h : Tendsto (fun i => iteratedFDeriv ℝ r (gseq i).euclideanCoefficients p) l
      (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients p))) :
    Tendsto (fun i => iteratedFDeriv ℝ r (fun z => (gseq i).inner z a b) p) l
      (𝓝 (iteratedFDeriv ℝ r (fun z => g.inner z a b) p)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ b).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)
  have heq (g' : RiemannianMetric n E) :
      iteratedFDeriv ℝ r (fun z => g'.inner z a b) p =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ r g'.euclideanCoefficients p) := by
    ext z
    exact g'.iteratedFDeriv_inner_eq p a b r z
  have hpost := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin r => E) (E →L[ℝ] E →L[ℝ] ℝ) ℝ L).continuous.tendsto _).comp h
  change Tendsto (fun i => L.compContinuousMultilinearMap
    (iteratedFDeriv ℝ r (gseq i).euclideanCoefficients p)) l
    (𝓝 (L.compContinuousMultilinearMap (iteratedFDeriv ℝ r g.euclideanCoefficients p))) at hpost
  rw [← heq g] at hpost
  exact hpost.congr (fun i => (heq (gseq i)).symm)



theorem tendsto_scalarCurvature_of_chart_metric_jets
    {n : ℕ} {M : Type u} {X : Type v} {ι : Type w} {l : Filter ι}
    [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ X]
    (gseq : ι → RiemannianMetric n M) (Dseq : ∀ i, LeviCivitaData (gseq i))
    (g : RiemannianMetric n X) (D : LeviCivitaData g)
    (qM : M) (qX : X) (p : EuclideanSpace ℝ (Fin n))
    (hpM : p ∈ (extChartAt (𝓡 n) qM).target)
    (hpX : p ∈ (extChartAt (𝓡 n) qX).target)
    (hjets : ∀ r : ℕ, r ≤ 2 →
      Tendsto (fun i => iteratedFDeriv ℝ r
        ((gseq i).pullbackCoefficients (extChartAt (𝓡 n) qM).symm) p) l
        (𝓝 (iteratedFDeriv ℝ r
          (g.pullbackCoefficients (extChartAt (𝓡 n) qX).symm) p))) :
    Tendsto (fun i => (Dseq i).scalarCurvature ((extChartAt (𝓡 n) qM).symm p)) l
      (𝓝 (D.scalarCurvature ((extChartAt (𝓡 n) qX).symm p))) := by
  classical
  choose gd hgd using fun i => exists_chart_scalar_realization (gseq i) (Dseq i) qM p hpM
  obtain ⟨gD, hcoeff, hscalar⟩ := exists_chart_scalar_realization g D qX p hpX
  have hbilinear (r : ℕ) (hr : r ≤ 2) :
      Tendsto (fun i => iteratedFDeriv ℝ r (gd i).1.euclideanCoefficients p) l
        (𝓝 (iteratedFDeriv ℝ r gD.1.euclideanCoefficients p)) := by
    rw [(hcoeff.iteratedFDeriv ℝ r).self_of_nhds]
    exact (hjets r hr).congr (fun i => (((hgd i).1.iteratedFDeriv ℝ r).self_of_nhds).symm)
  have h := LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets
    (fun i => (gd i).2) gD.2 p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (fun r hr a b => tendsto_scalar_jets_of_bilinear_jets p _ _ r (hbilinear r hr))
  rw [hscalar] at h
  exact h.congr (fun i => (hgd i).2)

end PoincareConjecture.SingularRegularLimit
