import PoincareConjecture.Proofs.M13.Carrier
import PoincareConjecture.Definitions.M14GeneralizedLGeometry










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}



noncomputable def rescalingCylinder
    (S : GeneralizedFlowSpacetime n X time I) (D : SpacetimeIntervalSystem)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (E : CompatibleSpacetimeCylinder S (D.interval K) C) :
    CompatibleSpacetimeCylinder (M13.parabolicSpacetime S Q hQ a)
      (D.interval (parabolicInterval Q hQ a K)) C := by
  let P := M13.parabolicIntervalTransport D Q hQ a
  let F := P.diffeomorph K
  let d := F.symm.prodCongr (Diffeomorph.refl (𝓡 n) C ∞)
  have hd : ContMDiff (spacetimeModel n) (spacetimeModel n) ∞ d := d.contMDiff
  refine {
    interval_subset := parabolicInterval_subset Q hQ a K I E.interval_subset
    toSpacetime := fun p => E.toSpacetime (d p)
    embedding := E.embedding.comp d.toHomeomorph.isEmbedding
    time_eq := ?_
    worldline_smooth := fun x => (E.worldline_smooth x).comp F.symm.contMDiff
    worldline_derivative := ?_
    smooth := E.smooth.comp hd
    differential_injective := ?_ }
  · intro p
    change parabolicTime Q a (S.timeFunction (E.toSpacetime (d p))) = p.1.val
    rw [E.time_eq]
    change parabolicTime Q a (((P.diffeomorph K).symm p.1 : _).val) = p.1.val
    rw [P.inverse_eq]
    exact parabolicTime_parabolicTimeInv Q hQ a p.1.val
  · intro t x
    change mfderiv (𝓡∂ 1) (spacetimeModel n)
      ((fun s : (D.interval K).Point => E.toSpacetime (s, x)) ∘ F.symm) t
      ((D.interval (parabolicInterval Q hQ a K)).positiveTangent t) = _
    rw [mfderiv_comp t ((E.worldline_smooth x).mdifferentiable (by simp) _)
      (F.symm.mdifferentiable (by simp) _)]
    change mfderiv (𝓡∂ 1) (spacetimeModel n)
      (fun s : (D.interval K).Point => E.toSpacetime (s, x)) (F.symm t)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) F.symm t
        ((D.interval (parabolicInterval Q hQ a K)).positiveTangent t)) = _
    rw [P.inverse_derivative, map_smul, E.worldline_derivative]
    rfl
  · intro p v w hvw
    apply (d.mfderivToContinuousLinearEquiv (by simp) p).injective
    apply E.differential_injective (d p)
    change mfderiv (spacetimeModel n) (spacetimeModel n) (E.toSpacetime ∘ d) p v =
      mfderiv (spacetimeModel n) (spacetimeModel n) (E.toSpacetime ∘ d) p w at hvw
    rw [mfderiv_comp p (E.smooth.mdifferentiable (by simp) _)
      (hd.mdifferentiable (by simp) _)] at hvw
    exact hvw



noncomputable def rescalingCylinderMetric
    (S : GeneralizedFlowSpacetime n X time I) (D : SpacetimeIntervalSystem)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (E : CompatibleSpacetimeCylinder S (D.interval K) C)
    (g : SpacetimeCylinderMetric E) :
    SpacetimeCylinderMetric (rescalingCylinder S D Q hQ a K E) := by
  let P := M13.parabolicIntervalTransport D Q hQ a
  refine {
    metric := fun s => M13.scaleSmoothMetric (g.metric (parabolicTimeInv Q a s)) Q hQ
    smooth := M13.scaled_reparameterized_smooth K g.metric g.smooth Q hQ a
    spatialTangentEquiv := fun t x =>
      (g.spatialTangentEquiv ((P.diffeomorph K).symm t) x).trans
        (M13.parabolicSpacetimeHorizontal S Q hQ a
          (E.toSpacetime ((P.diffeomorph K).symm t, x)))
    spatialTangentEquiv_eq := ?_
    metric_eq := ?_ }
  · intro t x v
    exact g.spatialTangentEquiv_eq ((P.diffeomorph K).symm t) x v
  · intro t x v w
    change (M13.scaleSmoothMetric (g.metric (parabolicTimeInv Q a (t : ℝ))) Q hQ).inner
        x v w =
      (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner
        (E.toSpacetime ((P.diffeomorph K).symm t, x))
        (M13.parabolicSpacetimeHorizontal S Q hQ a
          (E.toSpacetime ((P.diffeomorph K).symm t, x))
          (g.spatialTangentEquiv ((P.diffeomorph K).symm t) x v))
        (M13.parabolicSpacetimeHorizontal S Q hQ a
          (E.toSpacetime ((P.diffeomorph K).symm t, x))
          (g.spatialTangentEquiv ((P.diffeomorph K).symm t) x w))
    rw [M13.scaleSmoothMetric_inner, M13.parabolicSpacetime_metric]
    exact congrArg (Q * ·) (g.metric_eq ((P.diffeomorph K).symm t) x v w)



noncomputable def rescalingGaugeCover
    (S : GeneralizedFlowSpacetime n X time I) (D : SpacetimeIntervalSystem)
    (B : SpacetimeGaugeCover S D) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    SpacetimeGaugeCover (M13.parabolicSpacetime S Q hQ a) D := by
  let P := M13.parabolicIntervalTransport D Q hQ a
  refine {
    index := B.index
    interval := fun b => parabolicInterval Q hQ a (B.interval b)
    spatial := B.spatial
    cylinder := fun b => rescalingCylinder S D Q hQ a (B.interval b) (B.cylinder b)
    metric := fun b =>
      rescalingCylinderMetric S D Q hQ a (B.interval b) (B.cylinder b) (B.metric b)
    local_diffeomorph := ?_
    covers := ?_ }
  · intro b p
    change IsLocalDiffeomorphAt (spacetimeModel n) (spacetimeModel n) ∞
      ((B.cylinder b).toSpacetime ∘
        ((P.diffeomorph (B.interval b)).symm.prodCongr
          (Diffeomorph.refl (𝓡 n) (B.spatial b) ∞))) p
    exact IsLocalDiffeomorphAt.comp
      (hf := ((P.diffeomorph (B.interval b)).symm.prodCongr
        (Diffeomorph.refl (𝓡 n) (B.spatial b) ∞)).isLocalDiffeomorph p)
      (hg := B.local_diffeomorph b _)
  · intro p
    obtain ⟨b, q, hq⟩ := B.covers p
    refine ⟨b, (P.diffeomorph (B.interval b) q.1, q.2), ?_⟩
    change (B.cylinder b).toSpacetime
      (((P.diffeomorph (B.interval b)).symm
        (P.diffeomorph (B.interval b) q.1)), q.2) = p
    rw [Diffeomorph.symm_apply_apply]
    exact hq

end PoincareConjecture.M14
