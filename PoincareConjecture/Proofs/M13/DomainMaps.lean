import PoincareConjecture.Proofs.M13.Carrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem interval_subset_of_parabolic {K L : SpacetimeInterval}
    (h : (parabolicInterval Q hQ a K).domain ⊆
      (parabolicInterval Q hQ a L).domain) : K.domain ⊆ L.domain := by
  intro t ht
  exact (parabolicTime_mem_parabolicInterval_iff Q hQ a L t).1
    (h ((parabolicTime_mem_parabolicInterval_iff Q hQ a K t).2 ht))

theorem worldline_ext {time : X → ℝ} {I K : SpacetimeInterval}
    {S : GeneralizedFlowSpacetime n X time I} {T : SmoothSpacetimeInterval K}
    {e f : SpacetimeWorldline S T} (h : e.curve = f.curve) : e = f := by
  cases e
  cases f
  cases h
  rfl

theorem compatibleEmbedding_ext {time : X → ℝ} {I K : SpacetimeInterval}
    {S : GeneralizedFlowSpacetime n X time I} {T : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C]
    {e f : CompatibleSpacetimeEmbedding S T C} (h : e.toSpacetime = f.toSpacetime) :
    e = f := by
  cases e
  cases f
  cases h
  rfl

theorem compatibleCylinder_ext {time : X → ℝ} {I K : SpacetimeInterval}
    {S : GeneralizedFlowSpacetime n X time I} {T : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    {e f : CompatibleSpacetimeCylinder S T C} (h : e.toSpacetime = f.toSpacetime) :
    e = f := by
  cases e with
  | mk e he hi =>
    cases f with
    | mk f hf hj =>
      have hef := compatibleEmbedding_ext h
      cases hef
      rfl

noncomputable def transportedWorldline (K : SpacetimeInterval)
    (e : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K)) :
    SpacetimeWorldline (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) := by
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  let f := (P.diffeomorph K).symm
  refine {
    interval_subset := parabolicInterval_subset Q hQ a K A.interval e.interval_subset
    curve := e.curve ∘ f
    smooth := e.smooth.comp f.contMDiff
    time_eq := ?_
    derivative_eq := ?_ }
  · intro t
    change parabolicTime Q a (R.spacetime.timeFunction (e.curve (f t))) = t.val
    rw [e.time_eq]
    change parabolicTime Q a (parabolicTimeInv Q a t.val) = t.val
    exact parabolicTime_parabolicTimeInv Q hQ a t.val
  · intro t
    rw [mfderiv_comp t (e.smooth.mdifferentiable (by simp) _)
      (f.mdifferentiable (by simp) _)]
    change mfderiv (𝓡∂ 1) (spacetimeModel n) e.curve (f t)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) f t
        ((R.timeIntervals.interval (parabolicInterval Q hQ a K)).positiveTangent t)) = _
    rw [P.inverse_derivative, map_smul, e.derivative_eq]
    rfl

noncomputable def untransportedWorldline (K : SpacetimeInterval)
    (e : SpacetimeWorldline (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K))) :
    SpacetimeWorldline R.spacetime (R.timeIntervals.interval K) := by
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  let f := P.diffeomorph K
  refine {
    interval_subset := interval_subset_of_parabolic e.interval_subset
    curve := e.curve ∘ f
    smooth := e.smooth.comp f.contMDiff
    time_eq := ?_
    derivative_eq := ?_ }
  · intro t
    have h := e.time_eq (f t)
    change parabolicTime Q a (R.spacetime.timeFunction (e.curve (f t))) =
      parabolicTime Q a t.val at h
    exact (parabolicTimeOrderIso Q hQ a).injective h
  · intro t
    rw [mfderiv_comp t (e.smooth.mdifferentiable (by simp) _)
      (f.mdifferentiable (by simp) _)]
    change mfderiv (𝓡∂ 1) (spacetimeModel n) e.curve (f t)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) f t
        ((R.timeIntervals.interval K).positiveTangent t)) = _
    rw [P.derivative, map_smul, e.derivative_eq]
    change Q • ((1 / Q : ℝ) • R.spacetime.timeVector (e.curve (f t))) = _
    rw [smul_smul, one_div, mul_inv_cancel₀ hQ.ne', one_smul]
    rfl

noncomputable def worldlineEquiv (K : SpacetimeInterval) :
    SpacetimeWorldline R.spacetime (R.timeIntervals.interval K) ≃
      SpacetimeWorldline (parabolicSpacetime R.spacetime Q hQ a)
        (R.timeIntervals.interval (parabolicInterval Q hQ a K)) where
  toFun := transportedWorldline K
  invFun := untransportedWorldline K
  left_inv e := by
    apply worldline_ext
    funext t
    exact congrArg e.curve
      (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K).symm_apply_apply t)
  right_inv e := by
    apply worldline_ext
    funext t
    exact congrArg e.curve
      (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K).apply_symm_apply t)

noncomputable def transportedEmbedding {C : Type v} [TopologicalSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C) :
    CompatibleSpacetimeEmbedding (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C := by
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  let f := (P.diffeomorph K).symm
  refine {
    interval_subset := parabolicInterval_subset Q hQ a K A.interval e.interval_subset
    toSpacetime := fun p ↦ e.toSpacetime (f p.1, p.2)
    embedding := e.embedding.comp (f.toHomeomorph.prodCongr (Homeomorph.refl C)).isEmbedding
    time_eq := ?_
    worldline_smooth := fun x ↦ (e.worldline_smooth x).comp f.contMDiff
    worldline_derivative := ?_ }
  · intro t
    change parabolicTime Q a (R.spacetime.timeFunction (e.toSpacetime (f t.1, t.2))) = t.1.val
    rw [e.time_eq]
    exact parabolicTime_parabolicTimeInv Q hQ a t.1.val
  · intro t x
    change mfderiv (𝓡∂ 1) (spacetimeModel n)
      ((fun s ↦ e.toSpacetime (s, x)) ∘ f) t _ = _
    rw [mfderiv_comp t ((e.worldline_smooth x).mdifferentiable (by simp) _)
      (f.mdifferentiable (by simp) _)]
    change mfderiv (𝓡∂ 1) (spacetimeModel n) (fun s ↦ e.toSpacetime (s, x)) (f t)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) f t
        ((R.timeIntervals.interval (parabolicInterval Q hQ a K)).positiveTangent t)) = _
    rw [P.inverse_derivative, map_smul, e.worldline_derivative]
    rfl

noncomputable def untransportedEmbedding {C : Type v} [TopologicalSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C) :
    CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C := by
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  let f := P.diffeomorph K
  refine {
    interval_subset := interval_subset_of_parabolic e.interval_subset
    toSpacetime := fun p ↦ e.toSpacetime (f p.1, p.2)
    embedding := e.embedding.comp (f.toHomeomorph.prodCongr (Homeomorph.refl C)).isEmbedding
    time_eq := ?_
    worldline_smooth := fun x ↦ (e.worldline_smooth x).comp f.contMDiff
    worldline_derivative := ?_ }
  · intro t
    have h := e.time_eq (f t.1, t.2)
    change parabolicTime Q a (R.spacetime.timeFunction (e.toSpacetime (f t.1, t.2))) =
      parabolicTime Q a t.1.val at h
    exact (parabolicTimeOrderIso Q hQ a).injective h
  · intro t x
    change mfderiv (𝓡∂ 1) (spacetimeModel n)
      ((fun s ↦ e.toSpacetime (s, x)) ∘ f) t _ = _
    rw [mfderiv_comp t ((e.worldline_smooth x).mdifferentiable (by simp) _)
      (f.mdifferentiable (by simp) _)]
    change mfderiv (𝓡∂ 1) (spacetimeModel n) (fun s ↦ e.toSpacetime (s, x)) (f t)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) f t
        ((R.timeIntervals.interval K).positiveTangent t)) = _
    rw [P.derivative, map_smul, e.worldline_derivative]
    change Q • ((1 / Q : ℝ) • R.spacetime.timeVector (e.toSpacetime (f t, x))) = _
    rw [smul_smul, one_div, mul_inv_cancel₀ hQ.ne', one_smul]

noncomputable def embeddingEquiv (C : Type v) [TopologicalSpace C]
    (K : SpacetimeInterval) :
    CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C ≃
      CompatibleSpacetimeEmbedding (parabolicSpacetime R.spacetime Q hQ a)
        (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C where
  toFun := transportedEmbedding K
  invFun := untransportedEmbedding K
  left_inv e := by
    apply compatibleEmbedding_ext
    funext p
    change e.toSpacetime
      (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K).symm
        (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K) p.1), p.2) = _
    rw [Diffeomorph.symm_apply_apply]
  right_inv e := by
    apply compatibleEmbedding_ext
    funext p
    change e.toSpacetime
      (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K)
        (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K).symm p.1), p.2) = _
    rw [Diffeomorph.apply_symm_apply]

noncomputable def untransportedCylinder {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C) :
    CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C := by
  let f := (parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K
  let d := f.prodCongr (Diffeomorph.refl (𝓡 n) C ∞)
  refine {
    toCompatibleSpacetimeEmbedding := untransportedEmbedding K e.toCompatibleSpacetimeEmbedding
    smooth := e.smooth.comp d.contMDiff
    differential_injective := ?_ }
  intro p v w h
  apply (d.mfderivToContinuousLinearEquiv (by simp) p).injective
  apply e.differential_injective (d p)
  change mfderiv (spacetimeModel n) (spacetimeModel n) (e.toSpacetime ∘ d) p v =
    mfderiv (spacetimeModel n) (spacetimeModel n) (e.toSpacetime ∘ d) p w at h
  rw [mfderiv_comp p (e.smooth.mdifferentiable (by simp) _) (d.mdifferentiable (by simp) _)] at h
  exact h

noncomputable def cylinderEquiv (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) :
    CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C ≃
      CompatibleSpacetimeCylinder (parabolicSpacetime R.spacetime Q hQ a)
        (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C where
  toFun := transportedCylinder K
  invFun := untransportedCylinder K
  left_inv e := by
    apply compatibleCylinder_ext
    funext p
    change e.toSpacetime
      (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K).symm
        (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K) p.1), p.2) = _
    rw [Diffeomorph.symm_apply_apply]
  right_inv e := by
    apply compatibleCylinder_ext
    funext p
    change e.toSpacetime
      (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K)
        (((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K).symm p.1), p.2) = _
    rw [Diffeomorph.apply_symm_apply]

end PoincareConjecture.M13
