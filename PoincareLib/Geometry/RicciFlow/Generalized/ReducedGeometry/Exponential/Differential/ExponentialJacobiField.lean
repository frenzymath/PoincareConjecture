import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Construction.ExponentialSlices
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialJacobiData

/-!
# The actual Jacobi field along every supplied exponential family

Morgan-Tian Lemma 6.19, p. 114, and Proposition 6.30, pp. 118-119.
The supplied and canonical families agree on each open survival slice.
Their actual differentials agree, so the canonical Jacobi field on the
supplied path is its genuine exponential differential at every time.
-/

set_option autoImplicit false
-- The actual horizontal fibers and manifold tangents retain their fixed model values.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

private theorem horizontal_heq_of_val_eq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} {w : G.Horizontal r} (hv : v.val = w.val) : HEq v w := by
  cases h
  exact heq_of_eq (Subtype.ext hv)

/-- The supplied exponential differential equals the canonical actual
initial-value differential in the same horizontal fiber, including
physical endpoints, Lemma 6.19, p. 114. -/
theorem exponential_differential_heq_initialValue
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (W : G.Horizontal x) :
    HEq (E.differential Z s hs W) (initialValueDifferential G T x Z s W) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have heq : (fun A => E.gamma A s) =ᶠ[𝓝 Z] (fun A => initialValueCurve G T x A s) := by
    filter_upwards [(exponentialFamily_domain_slice_isOpen E s).mem_nhds hs] with A hA
    exact exponentialFamily_gamma_eq hM04 hM12 E hA
  have hd := congrArg (fun L : G.Horizontal x →L[ℝ] SpacetimeModelVector n => L W)
    (heq.mfderiv_eq (I := 𝓘(ℝ, G.Horizontal x)) (I' := spacetimeModel n))
  apply horizontal_heq_of_val_eq (exponentialFamily_gamma_eq hM04 hM12 E hs)
  exact (E.differential_pointwise_mfderiv Z s hs W).trans (hd.trans
    (initialValueDifferential_val hM04 hM12 E.base_time
      (exponentialFamily_domain_eq E ▸ hs) W).symm)

/-- The actual normalized Jacobi field on a supplied full path
equals its actual exponential differential at every prefix time,
Lemma 6.19, p. 114, and Proposition 6.30, pp. 118-119. -/
theorem exponentialJacobiField_heq_differential
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x) {b s : ℝ}
    (hb : (Z, b) ∈ E.domain) (hpos : 0 < b)
    (hs : s ∈ M14SqrtParameterInterval 0 (b ^ 2)) (hsurv : (Z, s) ∈ E.domain) :
    HEq ((initialValuePath_differentialData hM04 hM12
      (exponentialInitialValuePath E Z b hb hpos) W).field s) (E.differential Z s hsurv W) :=
  (initialValuePath_differentialField_heq hM04 hM12
    (exponentialInitialValuePath E Z b hb hpos) W hs).trans
      (exponential_differential_heq_initialValue hM04 hM12 E hsurv W).symm

end PoincareMT.M14
