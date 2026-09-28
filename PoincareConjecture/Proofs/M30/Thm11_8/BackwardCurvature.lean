import PoincareConjecture.Proofs.M30.Thm11_8.BackwardSpatialJets
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedClosedCurvature











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option synthInstance.maxHeartbeats 100000 in




theorem tendsto_backward_curvature
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    {s' s : ℝ} {T0 : ℝ≥0∞} {J : ℕ → Set ℝ}
    (hzero : s' < 0 ∧ 0 < s)
    {S : PointedFlowSequence 3 s' s}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k, RicciFlow 3 (S.carrier k).carrier (J k))
    (htime : ∀ A : ℝ, 0 < A → ENNReal.ofReal A < T0 →
      ∀ᶠ k in atTop, Icc (-A) 0 ⊆ J k)
    (F : RicciFlow 3 G.limitCarrier.carrier (blowupBackwardInterval T0)) :
    let ψ := fun (k : ℕ) (x : G.limitCarrier.carrier) =>
      ((G.embedding k).toFun (0, x)).2
    let f := fun (q : G.limitCarrier.carrier) k
        (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
      ((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients
        (ψ k ∘ (extChartAt (𝓡 3) q).symm) z.2
    let g := fun (q : G.limitCarrier.carrier)
        (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
      (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2
    (∀ (q : G.limitCarrier.carrier) (m : ℕ)
        (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))),
      IsCompact K → K ⊆ blowupBackwardInterval T0 ×ˢ
        (extChartAt (𝓡 3) q).target →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f q k)
          (blowupBackwardInterval T0 ×ˢ (extChartAt (𝓡 3) q).target))
        (iteratedFDerivWithin ℝ m (g q)
          (blowupBackwardInterval T0 ×ˢ (extChartAt (𝓡 3) q).target)) atTop K) →
    (∀ t ∈ blowupBackwardInterval T0, ∀ x : G.limitCarrier.carrier,
      Tendsto (fun k =>
        ((Fsrc (G.subsequence k)).connection t).negativeCurvaturePart (ψ k x))
        atTop (𝓝 0)) →
    ∀ t ∈ blowupBackwardInterval T0, ∀ x : G.limitCarrier.carrier,
      Tendsto (fun k =>
        ((Fsrc (G.subsequence k)).connection t).scalarCurvature (ψ k x))
        atTop (𝓝 ((F.connection t).scalarCurvature x)) ∧
      Tendsto (fun k =>
        ((Fsrc (G.subsequence k)).connection t).curvatureTensorNorm (ψ k x))
        atTop (𝓝 ((F.connection t).curvatureTensorNorm x)) ∧
      (F.connection t).NonnegativeCurvatureOperator x := by
  classical
  intro ψ f g hjets hdefect t ht x
  have hspatial := tendsto_backward_scalar_spatial_jets hSlice hzero G Fsrc htime F hjets
  let c := extChartAt (𝓡 3) x
  let p := c x
  have hp : p ∈ c.target := mem_extChartAt_target x
  have hcx : c.symm p = x := c.left_inv (mem_extChartAt_source x)
  obtain ⟨h, Dh, V, hVo, hpV, hV, heq⟩ :=
    G.limitCarrier.exists_local_coordinate_realization (F.metric t) x t p hp
  have hg : ∀ᶠ y in 𝓝 p, ∀ a b : Fin 3,
      h.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      G.limitCarrier.coordinateCoefficient x
        (fun _ y v w => G.limitCarrier.metricInner (F.metric t) y v w) a b (t, y) :=
    Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  have hlocaljets (r : ℕ) (_hr : r ≤ 2) (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => ((Fsrc (G.subsequence k)).metric t).pullbackCoefficients
          (ψ k ∘ c.symm) y (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) p) atTop
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => h.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)) := by
    rw [G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      x _ t p h hg r a b]
    exact hspatial x p hp t ht r a b
  have hsingle : IsCompact ({x} : Set G.limitCarrier.carrier) := isCompact_singleton
  obtain ⟨N, hN⟩ := G.exists_exhaustion_superset hsingle
  have hphi : ∀ᶠ k : ℕ in atTop, ∀ᶠ y in 𝓝 p,
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (ψ k ∘ c.symm) y ∧
        Function.Injective (mfderiv (𝓡 3) (𝓡 3) (ψ k ∘ c.symm) y) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    let W := c.target ∩ c.symm ⁻¹' G.exhaustion k
    have hW : IsOpen W :=
      (contMDiffOn_extChartAt_symm (n := ∞) x).continuousOn.isOpen_inter_preimage
        (isOpen_extChartAt_target x) (G.exhaustion_open k)
    have hpW : p ∈ W := by
      refine ⟨hp, ?_⟩
      change c.symm p ∈ G.exhaustion k
      rw [hcx]
      exact G.exhaustion_monotone hk (hN (mem_singleton x))
    filter_upwards [hW.mem_nhds hpW] with y hy
    have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
      (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy.1).contMDiffAt
        (extChartAt_target_mem_nhds' hy.1)
    have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (ψ k) (c.symm y) :=
      (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hy.2
    refine ⟨hf.comp y hc, ?_⟩
    rw [mfderiv_comp y (hf.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp))]
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    exact ((G.embedding k).spatialMap_mfderiv_injective
      (G.exhaustion_open k) hzero hy.2).comp hi.injective
  have hd : Tendsto (fun k =>
      ((Fsrc (G.subsequence k)).connection t).negativeCurvaturePart
        ((ψ k ∘ c.symm) p)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, hcx] using hdefect t ht x
  obtain ⟨hscalar, hoperator⟩ :=
    scalar_and_nonnegativeCurvatureOperator_of_pullback_metric_jets
      (fun k : ℕ => (Fsrc (G.subsequence k)).connection t)
      (fun k => ψ k ∘ c.symm) Dh p hphi hlocaljets hd
  have hnorm := LeviCivitaData.tendsto_curvatureTensorNorm_of_moving_scalar_pullback_jets
    (fun k : ℕ => (Fsrc (G.subsequence k)).connection t)
    (fun k => ψ k ∘ c.symm) Dh (fun _ : ℕ => p) p hphi hlocaljets
  have hmetric : ∀ y ∈ V, ∀ u v : TangentSpace (𝓡 3) y,
      h.inner y u v = (F.metric t).inner (c.symm y)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y u)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y v) := by
    intro y hy
    have hB : h.euclideanCoefficients y = (F.metric t).pullbackCoefficients c.symm y := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
      intro a
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
      exact heq y hy a
    intro u v
    exact congrArg (fun B => B u v) hB
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm V :=
    (contMDiffOn_extChartAt_symm (n := ∞) x).mono hV
  have hscalar_target : Dh.scalarCurvature p = (F.connection t).scalarCurvature x := by
    have hs := Dh.scalarCurvature_eq_of_local_isometry (F.connection t)
      hVo hsmooth hmetric hpV
    simpa only [hcx] using hs
  have hsign_target :
      Dh.NonnegativeCurvatureOperator p ↔ (F.connection t).NonnegativeCurvatureOperator x := by
    have hs := Dh.nonnegativeCurvatureOperator_iff_of_local_isometry (F.connection t)
      hVo hsmooth hmetric hpV
    simpa only [hcx] using hs
  have hnorm_target : Dh.curvatureTensorNorm p = (F.connection t).curvatureTensorNorm x := by
    have hn := G.limitCarrier.curvatureTensorNorm_eq_of_coordinate_germ
      (F.metric t) (F.connection t) x t p hp h Dh hg
    change Dh.curvatureTensorNorm p = (F.connection t).curvatureTensorNorm (c.symm p) at hn
    rw [hcx] at hn
    exact hn
  rw [hscalar_target] at hscalar
  rw [hnorm_target] at hnorm
  refine ⟨?_, ?_, hsign_target.mp hoperator⟩
  · simpa only [Function.comp_apply, hcx] using hscalar
  · simpa only [Function.comp_apply, hcx] using hnorm

end PoincareConjecture.M30
