import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.EuclideanNorm










noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData



theorem tendsto_curvatureTensorNorm_of_partialDiffeomorph_metric_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (gseq : ℕ → RiemannianMetric n M) (Dseq : ∀ k, LeviCivitaData (gseq k))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ∀ k, x ∈ (Φ k).source)
    (hjets : ∀ r : ℕ, r ≤ 2 →
      Tendsto (fun k => iteratedFDeriv ℝ r ((gseq k).pullbackCoefficients (Φ k)) x)
        atTop (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x))) :
    Tendsto (fun k => (Dseq k).curvatureTensorNorm (Φ k x)) atTop
      (𝓝 (D.curvatureTensorNorm x)) := by
  have hreal (k : ℕ) :
      ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (_D' : LeviCivitaData g') (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (Φ k).source ∧
          ∀ y ∈ V, g'.euclideanCoefficients y = (gseq k).pullbackCoefficients (Φ k) y := by
    apply RiemannianMetric.exists_local_realization (Φ k).open_source (hx k)
      ((gseq k).pullbackCoefficients (Φ k))
    · intro y hy
      exact ((gseq k).contDiffAt_pullbackCoefficients
        ((Φ k).contMDiffOn.contMDiffAt ((Φ k).open_source.mem_nhds hy))).contDiffWithinAt
    · intro y _ a b
      exact (gseq k).symm (Φ k y) _ _
    · intro y hy v hv
      apply (gseq k).pos (Φ k y)
      intro hz
      apply hv
      have hd : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (Φ k) y :=
        ⟨Φ k, hy, Set.eqOn_refl _ _⟩
      apply (hd.mfderivToContinuousLinearEquiv (by simp)).injective
      change mfderiv (𝓡 n) (𝓡 n) (Φ k) y v = mfderiv (𝓡 n) (𝓡 n) (Φ k) y 0
      rw [map_zero]
      convert! hz using 1
  choose gs Ds V hVo hxV hVsource heq using hreal
  have hnorm (k : ℕ) : (Ds k).curvatureTensorNorm x =
      (Dseq k).curvatureTensorNorm (Φ k x) := by
    apply (Ds k).curvatureTensorNorm_eq_of_local_isometry (Dseq k) (hVo k)
      ((Φ k).contMDiffOn.mono (hVsource k)) _ (hxV k)
    intro y hy a b
    exact congrArg (fun B => B a b) (heq k y hy)
  have hbilinear (r : ℕ) (hr : r ≤ 2) :
      Tendsto (fun k => iteratedFDeriv ℝ r (gs k).euclideanCoefficients x)
        atTop (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x)) := by
    apply (hjets r hr).congr
    intro k
    symm
    have hevent : (gs k).euclideanCoefficients =ᶠ[𝓝 x] (gseq k).pullbackCoefficients (Φ k) :=
      Filter.Eventually.mono ((hVo k).mem_nhds (hxV k)) (heq k)
    exact (hevent.iteratedFDeriv ℝ r).self_of_nhds
  let E := EuclideanSpace ℝ (Fin n)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hscalar (r : ℕ) (hr : r ≤ 2) (a c : Fin n) :
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (gs k).inner y (b a) (b c)) x)
        atTop (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x)) := by
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (b c)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b a))
    have heval (g' : RiemannianMetric n E) :
        iteratedFDeriv ℝ r (fun y => g'.inner y (b a) (b c)) x =
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ r g'.euclideanCoefficients x) := by
      ext v
      exact g'.iteratedFDeriv_inner_eq x (b a) (b c) r v
    have hh := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin r => E) (E →L[ℝ] E →L[ℝ] ℝ) ℝ L).continuous.tendsto _).comp
        (hbilinear r hr)
    change Tendsto (fun k => L.compContinuousMultilinearMap
      (iteratedFDeriv ℝ r (gs k).euclideanCoefficients x)) atTop
      (𝓝 (L.compContinuousMultilinearMap (iteratedFDeriv ℝ r g.euclideanCoefficients x))) at hh
    rw [← heval g] at hh
    exact hh.congr (fun k => (heval (gs k)).symm)
  exact (tendsto_curvatureTensorNorm_of_scalar_metric_jets Ds D x b hscalar).congr hnorm

end PoincareConjecture.LeviCivitaData
