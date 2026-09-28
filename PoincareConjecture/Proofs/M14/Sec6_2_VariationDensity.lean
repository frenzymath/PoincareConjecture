import PoincareConjecture.Proofs.M14.Sec6_2_VariationTorsion
import PoincareConjecture.Proofs.M14.Sec6_2_MovingMetric









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}



theorem hasDerivAt_variationActionDensity
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (V : M14LVariationData G p R)
    {s v : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (hv : v ∈ V.parameterDomain)
    (E : M14PullbackExtension G (fun u => V.squareFamily s u) V.parameterDomain
      (variationSquareVelocity V s)) :
    HasDerivAt (fun u => variationActionDensity V (s, u))
      (2 * s ^ 2 * M14HorizontalScalarDifferential G (V.squareFamily s v)
          (M14EndpointVariationField V s v).val +
        G.spacetime.horizontalMetric.inner (V.squareFamily s v)
          (variationSquareVelocity V s v)
          (M14HorizontalCovariantDerivative G (fun u => V.squareFamily s u)
            V.parameterDomain (variationSquareVelocity V s) E v)) v := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hγ := ((variation_parameter_smooth V hs v hv).contMDiffAt
    (hP.mem_nhds hv)).mdifferentiableAt (by simp)
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hR := (H.scalar_smooth.mdifferentiable (by simp) (V.squareFamily s v)).hasMFDerivAt
  have hscalar := (hR.comp v hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun u => horizontalScalarCurvature G.leafwise (V.squareFamily s u))
    (M14HorizontalScalarDifferential G (V.squareFamily s v)
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => V.squareFamily s u) v 1)) v
    at hscalar
  rw [← endpointVariationField_val_eq_tangent V hs hv] at hscalar
  have hmetric := horizontalCovariantDerivative_metric_product E E hv
    (hP.uniqueDiffOn v hv) hγ.mdifferentiableWithinAt
  have hclock : (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
      (V.squareFamily s v)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => V.squareFamily s u)
        V.parameterDomain v (1 : ℝ))) = 0 := by
    simpa only [mfderivWithin_of_mem_nhds (hP.mem_nhds hv)] using
      variation_parameter_clock_eq_zero V hs hv
  rw [hclock, mul_zero, zero_mul, sub_zero,
    G.spacetime.horizontalMetric.symm (V.squareFamily s v)
      (M14HorizontalCovariantDerivative G (fun u => V.squareFamily s u)
        V.parameterDomain (variationSquareVelocity V s) E v)] at hmetric
  have h := (hscalar.const_mul (2 * s ^ 2)).add
    ((hmetric.hasDerivAt (hP.mem_nhds hv)).const_mul (1 / 2 : ℝ))
  convert! h using 1
  ring

private theorem horizontal_inner_heq {q r : G.Point} (h : q = r)
    {a b : G.Horizontal q} {c d : G.Horizontal r} (ha : HEq a c) (hb : HEq b d) :
    G.spacetime.horizontalMetric.inner q a b = G.spacetime.horizontalMetric.inner r c d := by
  cases h
  cases ha
  cases hb
  rfl

private theorem horizontal_scalar_heq {q r : G.Point} (h : q = r)
    {a : G.Horizontal q} {b : G.Horizontal r} (ha : HEq a b) :
    M14HorizontalScalarDifferential G q a.val = M14HorizontalScalarDifferential G r b.val := by
  cases h
  cases ha
  rfl

private theorem horizontal_transport_heq {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : HEq (h.symm ▸ v : G.Horizontal r) v := by
  cases h
  rfl



theorem hasDerivAt_variationActionDensity_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    HasDerivAt (fun u => variationActionDensity V (s, u))
      (2 * s ^ 2 * M14HorizontalScalarDifferential G (R.curve s) (M14VariationField V s).val +
        G.spacetime.horizontalMetric.inner (R.curve s) (R.horizontal_velocity s)
          (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂)
            (M14VariationField V) D.variation_extension s)) 0 := by
  have hsC : s ∈ M14SqrtParameterInterval τ₁ τ₂ := Ioo_subset_Icc_self hs
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  obtain ⟨E⟩ := exists_variation_velocity_parameter_extension V hsC
  have h := hasDerivAt_variationActionDensity hM12 V hsC hzero E
  have hY : HEq (M14EndpointVariationField V s 0) (M14VariationField V s) :=
    (horizontal_transport_heq (V.square_base s) _).symm
  have hA : HEq (variationSquareVelocity V s 0) (R.horizontal_velocity s) := by
    rw [variationSquareVelocity_zero V hsC]
    exact horizontal_transport_heq (V.square_base s).symm _
  have hD := (variation_covariantDerivative_commute hCoordinates V D hs E).symm
  rw [horizontal_scalar_heq (V.square_base s) hY,
    horizontal_inner_heq (V.square_base s) hA hD] at h
  exact h

end PoincareConjecture.M14
