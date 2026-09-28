import PoincareConjecture.Proofs.M14.Sec6_6_RescalingGeometry
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackReparametrization










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)



theorem rescalingHorizontalConnection (V : HorizontalSection G.spacetime)
    (p : G.Point) (Z : TangentSpace (spacetimeModel n) p) :
    rawHorizontalCovariantDerivative (rescalingTransport hM12 hM13 G Q hQ a).leafwise
      (rescalingHorizontalSection G.spacetime Q hQ a V) p Z =
      M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p
        (rawHorizontalCovariantDerivative G.leafwise V p Z) := by
  have hfactor (c : ℝ) : (Q * c) * (1 / Q) = c := by field_simp [hQ.ne']
  unfold rawHorizontalCovariantDerivative
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply]
  change rawLeafwiseCovariantDerivative (M13.parabolicLeafwiseConnection G.leafwise Q hQ a)
      (rescalingHorizontalSection G.spacetime Q hQ a V) p
      ((M13.parabolicSpacetime G.spacetime Q hQ a).horizontalProjection p Z) +
    mfderiv (spacetimeModel n) 𝓘(ℝ)
      (fun q : G.Point => parabolicTime Q a (G.spacetime.timeFunction q)) p Z •
      horizontalTimeBracket (M13.parabolicSpacetime G.spacetime Q hQ a)
        (rescalingHorizontalSection G.spacetime Q hQ a V) p = _
  have ht := M13.parabolicClock_derivative G.spacetime Q a p Z
  dsimp only at ht
  erw [M13.parabolicSpacetime_projection, rescalingTimeBracket, ht]
  change rawLeafwiseCovariantDerivative (M13.parabolicLeafwiseConnection G.leafwise Q hQ a)
      (fun q => M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a q (V q)) p
      (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a p
        (G.spacetime.horizontalProjection p Z)) + _ = _
  erw [M13.parabolic_leafwise_chosen]
  simp only [map_add, map_smul]
  congr 1
  apply Subtype.ext
  let c : ℝ := mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction p Z
  change (Q * c) •
      ((1 / Q : ℝ) • (horizontalTimeBracket G.spacetime V p).val) =
    c • (horizontalTimeBracket G.spacetime V p).val
  rw [smul_smul, hfactor]

private theorem horizontalMap_hasDerivAt {time' : X → ℝ} {I' : SpacetimeInterval}
    (S : GeneralizedFlowSpacetime n X time I)
    (S' : GeneralizedFlowSpacetime n X time' I') (p : S.Point) (q : S'.Point)
    (L : S.Horizontal p →L[ℝ] S'.Horizontal q)
    (f : ℝ → S.Horizontal p) (d : S.Horizontal p) (s : ℝ) (hd : HasDerivAt f d s) :
    HasDerivAt (fun r => L (f r)) (L d) s := by
  let g := S.horizontalMetric.toRiemannianMetric
  let g' := S'.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (S.Horizontal p) :=
    (g.toCore p).toNormedAddCommGroupOfTopology (g.continuousAt p) (g.isVonNBounded p)
  let : NormedSpace ℝ (S.Horizontal p) :=
    (g.toCore p).toNormedSpaceOfTopology (g.continuousAt p) (g.isVonNBounded p)
  let : NormedAddCommGroup (S'.Horizontal q) :=
    (g'.toCore q).toNormedAddCommGroupOfTopology (g'.continuousAt q) (g'.isVonNBounded q)
  let : NormedSpace ℝ (S'.Horizontal q) :=
    (g'.toCore q).toNormedSpaceOfTopology (g'.continuousAt q) (g'.isVonNBounded q)
  exact L.hasFDerivAt.comp_hasDerivAt s hd

private theorem horizontal_hasDerivAt_deriv
    (S : GeneralizedFlowSpacetime n X time I) (p : S.Point)
    (f : ℝ → S.Horizontal p) (d : S.Horizontal p) (s : ℝ) (hd : HasDerivAt f d s) :
    deriv f s = d := by
  let g := S.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (S.Horizontal p) :=
    (g.toCore p).toNormedAddCommGroupOfTopology (g.continuousAt p) (g.isVonNBounded p)
  let : NormedSpace ℝ (S.Horizontal p) :=
    (g.toCore p).toNormedSpaceOfTopology (g.continuousAt p) (g.isVonNBounded p)
  exact hd.deriv




noncomputable def rescalingPullbackExtension
    {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}
    (E : M14PullbackExtension G γ J Y) :
    M14PullbackExtension (rescalingTransport hM12 hM13 G Q hQ a) γ J
      (fun s => M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s) (Y s)) where
  extension := fun r => rescalingHorizontalSection G.spacetime Q hQ a (E.extension r)
  domain := E.domain
  domain_open := E.domain_open
  graph_mem := E.graph_mem
  spatial_smooth := fun r => rescalingHorizontalSection_smooth G.spacetime Q hQ a
    (E.extension r) E.domain (E.spatial_smooth r)
  joint_smooth := by
    obtain ⟨U, hU, hgraph, hsmooth⟩ := E.joint_smooth
    exact ⟨U, hU, hgraph,
      (M13.parabolicSpacetimeHorizontal_smooth G.spacetime Q hQ a).comp_contMDiffOn hsmooth⟩
  agrees := by
    intro s hs
    exact congrArg (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s)) (E.agrees s hs)
  parameter_derivative := by
    intro s hs
    obtain ⟨d, hd⟩ := E.parameter_derivative s hs
    refine ⟨M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s) d, ?_⟩
    exact horizontalMap_hasDerivAt G.spacetime (M13.parabolicSpacetime G.spacetime Q hQ a)
      (γ s) (γ s) (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s)).toContinuousLinearMap
      (fun r => E.extension r (γ s)) d s hd



theorem rescalingPullbackDerivative
    {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}
    (E : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ J) :
    M14HorizontalCovariantDerivative (rescalingTransport hM12 hM13 G Q hQ a) γ J
      (fun r => M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ r) (Y r))
      (rescalingPullbackExtension hM12 hM13 G Q hQ a E) s =
      M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s)
        (M14HorizontalCovariantDerivative G γ J Y E s) := by
  obtain ⟨d, hd⟩ := E.parameter_derivative s hs
  have htrans := horizontalMap_hasDerivAt G.spacetime (M13.parabolicSpacetime G.spacetime Q hQ a)
    (γ s) (γ s) (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s)).toContinuousLinearMap
    (fun r => E.extension r (γ s)) d s hd
  have hparam := horizontal_hasDerivAt_deriv (M13.parabolicSpacetime G.spacetime Q hQ a)
    (γ s) _ _ s htrans
  have hd' := horizontal_hasDerivAt_deriv G.spacetime (γ s) _ d s hd
  change deriv (fun r => M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s)
    (E.extension r (γ s))) s = M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s) d at hparam
  change deriv (fun r => M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ s)
      (E.extension r (γ s))) s +
    rawHorizontalCovariantDerivative (M13.parabolicLeafwiseConnection G.leafwise Q hQ a)
      (rescalingHorizontalSection G.spacetime Q hQ a (E.extension s)) (γ s)
      (mfderivWithin 𝓘(ℝ, ℝ) (spacetimeModel n) γ J s 1) = _
  rw [hparam]
  erw [rescalingHorizontalConnection hM12 hM13 G Q hQ a (E.extension s) (γ s)]
  simp only [M14HorizontalCovariantDerivative, map_add, hd']



theorem rescalingScalarDifferential (p : G.Point) (Z : TangentSpace (spacetimeModel n) p) :
    M14HorizontalScalarDifferential (rescalingTransport hM12 hM13 G Q hQ a) p Z =
      Q⁻¹ * M14HorizontalScalarDifferential G p Z := by
  have hscalar := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have heq : horizontalScalarCurvature (rescalingTransport hM12 hM13 G Q hQ a).leafwise =
      (fun q => Q⁻¹ * horizontalScalarCurvature G.leafwise q) :=
    funext (rescalingTransport_scalar hM12 hM13 G Q hQ a)
  unfold M14HorizontalScalarDifferential
  rw [heq, mvfderiv_fun_mul mdifferentiableAt_const
    (hscalar.scalar_smooth.mdifferentiable (by simp) p)]
  simp only [mvfderiv_const, smul_zero, add_zero, smul_apply, smul_eq_mul]

end PoincareConjecture.M14
