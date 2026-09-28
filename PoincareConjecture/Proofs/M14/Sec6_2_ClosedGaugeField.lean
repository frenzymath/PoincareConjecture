import PoincareConjecture.Proofs.M14.Sec6_2_LocalTestField
import PoincareConjecture.Proofs.M14.Sec6_4_FixedEndpointBoundary

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  (R : M14SquareRootPath G p) (j : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j) (η : ℝ → EuclideanSpace ℝ (Fin n))

private theorem horizontal_transport_val {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : (h.symm ▸ v : G.Horizontal r).val = v.val := by
  cases h
  rfl

theorem variationField_supportedGauge_val_at (V : M14LVariationData G p R) {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval a b)
    (hV : ∀ v, V.squareFamily s v = supportedGaugeFamily R j lift η (s, v))
    (hright : (G.gaugeCover.cylinder j).toSpacetime (lift (R.curve s)) = R.curve s) :
    (M14VariationField V s).val =
      ((G.gaugeCover.metric j).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 (η s)).val := by
  have htransport : (M14VariationField V s).val = (M14EndpointVariationField V s 0).val :=
    horizontal_transport_val (V.square_base s) _
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  rw [htransport, endpointVariationField_val_eq_tangent V hs hzero]
  have heq : (fun v => V.squareFamily s v) =
      (fun v => gaugeShiftFamily R j lift η (s, v)) :=
    funext (fun v => (hV v).trans (supportedGaugeFamily_eq_gauge R j lift η hright))
  rw [heq]
  exact gaugeShiftFamily_parameter_mfderiv R j lift η s

theorem variationField_supportedGauge_eq_zero (V : M14LVariationData G p R) {s : ℝ}
    (hV : ∀ v, V.squareFamily s v = supportedGaugeFamily R j lift η (s, v))
    (hs : s ∉ tsupport η) : M14VariationField V s = 0 := by
  apply variationField_eq_zero_of_constant V
  intro v _
  rw [hV v, hV 0, supportedGaugeFamily_eq_of_not_tsupport R j lift η hs,
    supportedGaugeFamily_eq_of_not_tsupport R j lift η hs]

end PoincareConjecture.M14
