import PoincareConjecture.Proofs.M14.Sec6_3_EndpointCost
import PoincareConjecture.Proofs.M14.Sec6_3_EndpointLineField
import PoincareConjecture.Proofs.M14.Sec6_3_ParameterLineVariation
import PoincareConjecture.Proofs.M14.Sec6_3_ParameterActionDifferential

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_heq_of_val_eq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} {w : G.Horizontal r} (hv : v.val = w.val) : HEq v w := by
  cases h
  exact heq_of_eq (Subtype.ext hv)

private theorem inner_pair_heq {q r : G.Point} (h : q = r)
    {v w : G.Horizontal q} {v' w' : G.Horizontal r} (hv : HEq v v') (hw : HEq w w') :
    G.spacetime.horizontalMetric.inner q v w = G.spacetime.horizontalMetric.inner r v' w' := by
  cases h
  cases hv
  cases hw
  rfl

namespace GaugeEndpointFamily

variable {f : ℝ × ℝ → G.Point} {U : Set ℝ} {T B c : ℝ}
  {j : G.gaugeCover.index}
  {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j}
  (D : GaugeEndpointFamily f U T 0 B c 0 j lift)

theorem prefixAction_fderiv_of_velocity
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hc : c ∈ Ioo 0 B) {x y : G.Point} {p : M14BackwardPath G T 0 (c ^ 2) x y}
    (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 (c ^ 2)) R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval 0 (c ^ 2), ∀ W,
      M14SquareRootEulerResidual G R E s W = 0)
    (r : ℝ) (hr : (r, (lift (f (c, r))).2.val) ∈ D.parameters)
    (hbase : ∀ s ∈ Icc 0 c, f (s, r) = R.curve s)
    (hleft : ∀ u ∈ U, f (0, u) = x) (ξ : EuclideanSpace ℝ (Fin n))
    (hvel : HEq (R.horizontal_velocity c) ((G.gaugeCover.metric j).spatialTangentEquiv
      (lift (f (c, 0))).1 (lift (f (c, r))).2 ξ))
    (d : ℝ × EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ D.prefixAction (r, (lift (f (c, r))).2.val) d =
      ((G.gaugeCover.metric j).metric (lift (f (c, 0))).1.val).inner (lift (f (c, r))).2 ξ d.2 := by
  have hC : M14SqrtParameterInterval 0 (c ^ 2) = Icc 0 c := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hc.1.le]
  have hsub : M14SqrtParameterInterval 0 (c ^ 2) ⊆ Icc 0 B :=
    fun _ hs => ⟨(hC ▸ hs).1, (hC ▸ hs).2.trans hc.2.le⟩
  let z : ℝ × EuclideanSpace ℝ (Fin n) := (r, (lift (f (c, r))).2.val)
  have hzero (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0 (c ^ 2)) :
      D.family (s, z) = R.curve s :=
    (D.recovery z hr s (hsub hs)).trans (hbase s (hC ▸ hs))
  obtain ⟨V, hparam, hV⟩ := exists_parameterLineVariation hM12 R D.family D.parameters_open
    D.smooth hsub D.clock z d hr hzero
  have hs0 : (0 : ℝ) ∈ M14SqrtParameterInterval 0 (c ^ 2) := by
    rw [hC]
    exact ⟨le_rfl, hc.1.le⟩
  have hsc : c ∈ M14SqrtParameterInterval 0 (c ^ 2) := by
    rw [hC]
    exact ⟨hc.1.le, le_rfl⟩
  have hfield0 : M14VariationField V (Real.sqrt 0) = 0 := by
    rw [Real.sqrt_zero]
    exact D.variationField_line_initial_zero V z d hparam (hV 0 hs0) hleft
  have hdiff : DifferentiableAt ℝ
      (squareFamilyAction G D.family (Icc 0 B) (Real.sqrt 0) (Real.sqrt (c ^ 2))) z := by
    rw [Real.sqrt_zero, Real.sqrt_sq hc.1.le]
    exact (D.prefixAction_contDiffAt hM12 hc hr).differentiableAt (by simp)
  have hderiv := fderiv_squareFamilyAction_euler_line hCoordinates hM12 E hEuler V D.family
    D.smooth hsub D.clock z d hparam hV hfield0 hdiff
  have hfun : squareFamilyAction G D.family (Icc 0 B) (Real.sqrt 0) (Real.sqrt (c ^ 2)) =
      D.prefixAction := by
    rw [Real.sqrt_zero, Real.sqrt_sq hc.1.le]
    rfl
  rw [hfun] at hderiv
  obtain ⟨hy, hfield⟩ := D.variationField_line_marked V hsc z d hr hparam (hV c hsc)
  obtain ⟨hy', hmark⟩ := D.marked z hr
  have hpoint : R.curve c = (G.gaugeCover.cylinder j).toSpacetime
      ((lift (f (c, 0))).1, (lift (f (c, r))).2) :=
    (hzero c hsc).symm.trans hmark
  have hfield' : HEq (M14VariationField V c) ((G.gaugeCover.metric j).spatialTangentEquiv
      (lift (f (c, 0))).1 (lift (f (c, r))).2 d.2) :=
    horizontal_heq_of_val_eq hpoint hfield
  have hpair := inner_pair_heq hpoint hvel hfield'
  rw [← (G.gaugeCover.metric j).metric_eq] at hpair
  have hboundary := congrArg (fun s => G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (M14VariationField V s)) (Real.sqrt_sq hc.1.le)
  exact hderiv.trans (hboundary.trans hpair)

end GaugeEndpointFamily

end PoincareConjecture.M14
