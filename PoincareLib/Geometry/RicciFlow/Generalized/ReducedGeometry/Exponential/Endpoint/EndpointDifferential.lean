import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian

/-!
# The actual derivative in the endpoint Jacobian

Morgan-Tian Proposition 6.28, p. 117, and Lemma 6.71, p. 141. The stable
set's derivative identity identifies the frozen endpoint tangent map with
the manifold derivative of its actual slice endpoint map.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
  {H : M14StableSet G T τ x E}

private theorem horizontal_map_transport_val {p q : G.Point} (h : p = q)
    (A : G.Horizontal x →L[ℝ] G.Horizontal p) (v : G.Horizontal x) :
    ((h ▸ A : G.Horizontal x →L[ℝ] G.Horizontal q) v).val = (A v).val := by
  cases h
  rfl

private theorem tangent_transport_val {p q : G.Point} (h : p = q)
    (v : TangentSpace (spacetimeModel n) p) :
    (show SpacetimeModelVector n from
      (h ▸ v : TangentSpace (spacetimeModel n) q)) = v := by
  cases h
  rfl

/-- The tangent map used in the metric Jacobian is the actual slice
derivative, as required by Morgan-Tian Lemma 6.71, p. 141. -/
theorem endpointTangentDifferential_eq_mfderiv
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) :
    M14EndpointTangentDifferential G Z hZ =
      M14EndpointSliceMfderiv G H.endpoint_slice_map Z := by
  ext v
  apply ((G.slices (T - τ)).tangentEquiv (H.endpoint_slice_map Z)).injective
  simp only [M14EndpointTangentDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [horizontal_map_transport_val]
  have hd := H.endpoint_slice_differential Z hZ v
  have hmodel := congrArg
    (fun w : TangentSpace (spacetimeModel n) (H.endpoint_map Z) =>
      (show SpacetimeModelVector n from w)) hd
  have heq := hmodel.symm
  simp only [tangent_transport_val] at heq
  exact heq

end PoincareMT.M14
