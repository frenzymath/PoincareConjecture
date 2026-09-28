import PoincareConjecture.Proofs.M14.Sec6_3_MaximalSmooth

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

noncomputable def initialValueDifferential
    (G : GeneralizedLGeometryTransport n X time I) (T : ℝ) (x : G.Point)
    (Z : G.Horizontal x) (s : ℝ) :
    G.Horizontal x →L[ℝ] G.Horizontal (initialValueCurve G T x Z s) :=
  letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  (G.spacetime.horizontalProjection (initialValueCurve G T x Z s)).comp
    (M14InitialVectorDerivative G (initialValueCurve G T x) s Z)

theorem initialValueCurve_initialVectorDerivative_zero (Z : G.Horizontal x) :
    M14InitialVectorDerivative G (initialValueCurve G T x) 0 Z = 0 := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  unfold M14InitialVectorDerivative
  have hcurve : (fun V => initialValueCurve G T x V 0) = fun _ => x :=
    funext initialValueCurve_zero
  rw [hcurve]
  exact mfderiv_const

theorem initialValueCurve_initialVectorDerivative_clock
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ initialValueDomain G T x) (W : G.Horizontal x) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
      (initialValueCurve G T x Z s)
      (M14InitialVectorDerivative G (initialValueCurve G T x) s Z W)) = 0 := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  rcases eq_or_lt_of_le (initialValueDomain_nonneg hs) with hs0 | hs0
  · subst s
    rw [initialValueCurve_initialVectorDerivative_zero]
    simp only [zero_apply, map_zero]
    rfl
  obtain ⟨U, hU, hZU, htube, hsm⟩ :=
    initialValueCurve_smooth_prefix hM04 hM12 hbase hs0 hs
  have hslice : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) ∞
      (fun V => initialValueCurve G T x V s) U :=
    hsm.comp (contMDiff_id.prodMk (contMDiff_const (c := s))).contMDiffOn
      (fun _ hV => ⟨hV, hs0.le, le_rfl⟩)
  have hdiff := ((hslice Z hZU).contMDiffAt (hU.mem_nhds hZU)).mdifferentiableAt
    (by simp)
  have htime : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have ht := (htime.mdifferentiable (by simp)
    (initialValueCurve G T x Z s)).hasMFDerivAt.comp Z hdiff.hasMFDerivAt
  have hc : HasFDerivAt (fun V => G.spacetime.timeFunction (initialValueCurve G T x V s))
      (0 : G.Horizontal x →L[ℝ] ℝ) Z := by
    apply (hasFDerivAt_const (T - s ^ 2) Z).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hZU] with V hV
    exact initialValueCurve_clock hbase (htube ⟨hV, hs0.le, le_rfl⟩)
  set_option backward.isDefEq.respectTransparency false in
    exact DFunLike.congr_fun (ht.hasFDerivAt.unique hc) W

set_option backward.isDefEq.respectTransparency false in

theorem initialValueDifferential_val
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ initialValueDomain G T x) (W : G.Horizontal x) :
    (initialValueDifferential G T x Z s W).val =
      M14InitialVectorDerivative G (initialValueCurve G T x) s Z W := by
  let v : TangentSpace (spacetimeModel n) (initialValueCurve G T x Z s) :=
    M14InitialVectorDerivative G (initialValueCurve G T x) s Z W
  change (G.spacetime.horizontalProjection _ v).val = v
  rw [G.spacetime.horizontalProjection_eq]
  change v - (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
    (initialValueCurve G T x Z s) v) •
      G.spacetime.timeVector (initialValueCurve G T x Z s) = v
  rw [initialValueCurve_initialVectorDerivative_clock hM04 hM12 hbase hs W,
    zero_smul, sub_zero]

end PoincareConjecture.M14
