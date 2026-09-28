import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartContact
import PoincareConjecture.Proofs.M14.Sec6_3_ActionFirstVariation
import PoincareConjecture.Proofs.M14.Sec6_2_SquareEuler
import PoincareConjecture.Proofs.M14.Sec6_4_FieldRealization
import PoincareConjecture.Proofs.M14.Sec6_4_AdaptedScale
import PoincareConjecture.Proofs.M14.Mathlib.SectionThroughVector

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

private theorem scalar_transport {q r : G.Point} (h : q = r)
    (f : G.Point → ℝ) (A : G.Horizontal q) :
    mvfderiv (spacetimeModel n) f r (h ▸ A).val =
      mvfderiv (spacetimeModel n) f q A.val := by
  cases h
  rfl

theorem positiveStart_variationEndpoint_hasDerivAt
    (V : M14LVariationData G p R) {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval a b) {f : G.Point → ℝ}
    (hf : MDifferentiableAt (spacetimeModel n) (𝓘(ℝ, ℝ)) f (R.curve s)) :
    HasDerivAt (fun v => f (V.squareFamily s v))
      (mvfderiv (spacetimeModel n) f (R.curve s) (M14VariationField V s).val) 0 := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hγ := ((variation_parameter_smooth V hs).contMDiffAt
    (hP.mem_nhds hzero)).mdifferentiableAt (by simp)
  have hf' : MDifferentiableAt (spacetimeModel n) (𝓘(ℝ, ℝ)) f
      (V.squareFamily s 0) := V.square_base s ▸ hf
  have h := (hf'.hasMFDerivAt.comp 0 hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun v => f (V.squareFamily s v))
    (mvfderiv (spacetimeModel n) f (V.squareFamily s 0)
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (V.squareFamily s) 0 1)) 0 at h
  rw [← endpointVariationField_val_eq_tangent V hs hzero] at h
  exact (scalar_transport (V.square_base s) f (M14EndpointVariationField V s 0)) ▸ h

theorem positiveStart_exists_terminalVariation
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (W : G.Horizontal (R.curve (Real.sqrt b))) :
    ∃ V : M14LVariationData G p R, V.left_endpoint_fixed ∧
      M14VariationField V (Real.sqrt a) = 0 ∧
      M14VariationField V (Real.sqrt b) = W := by
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  obtain ⟨Z, hZ, hZend⟩ := FiberBundle.exists_contMDiff_section_through
    (I := spacetimeModel n) (F := EuclideanSpace ℝ (Fin n)) W
  obtain ⟨EZ⟩ := exists_pullbackExtension_Icc (G := G) (γ := R.curve)
    (Y := fun r => Z (R.curve r)) hab
      (hZ.comp_contMDiffOn (R.smooth.mono R.interval_subset))
  let Y := horizontalAdaptedField (Real.sqrt a) (Real.sqrt b) (fun r => Z (R.curve r))
  have hend := horizontalAdaptedField_endpoints (P := fun r => Z (R.curve r)) hab
  have hY := pullbackExtension_field_contMDiffOn (horizontalAdaptedExtension EZ)
    (R.smooth.mono R.interval_subset)
  obtain ⟨V, hfix, hfield, _⟩ :=
    exists_initialFixed_variation_of_smooth_horizontalField R hM12 Y hY hend.1
  refine ⟨V, hfix, (hfield _ ⟨le_rfl, hab.le⟩).trans hend.1, ?_⟩
  exact (hfield _ ⟨hab.le, le_rfl⟩).trans (hend.2.trans hZend)

theorem positiveStart_horizontal_differential
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hp : M14IsMinimizing p)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U)
    (W : G.Horizontal (R.curve (Real.sqrt b))) :
    mvfderiv (spacetimeModel n) (M14ReducedLengthAt G T a x)
        (R.curve (Real.sqrt b)) W.val =
      G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
        (R.horizontal_velocity (Real.sqrt b)) W / (2 * Real.sqrt b) := by
  have hb := p.tau_nonneg.trans_lt p.tau_lt
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees _ hs, Real.sq_sqrt hb.le, p.curve_end]
  have hRU : R.curve (Real.sqrt b) ∈ U := by rwa [hpoint]
  obtain ⟨V, hfix, hleft, hright⟩ := positiveStart_exists_terminalVariation hM12 W
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  have hfirst := firstVariation_euler_fixedInitial hCoordinates hM12 E
    (fun _ ht Z => squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hp E ht Z)
    V hleft
  rw [hright] at hfirst
  have hscalar := positiveStart_variationEndpoint_hasDerivAt V hs
    (((hf _ hRU).contMDiffAt (hU.mem_nhds hRU)).mdifferentiableAt
      (by simp))
  rw [hright] at hscalar
  have hgap := isLocalMin_variationAction_gap_of_smooth_minimizing hM12 V hp hfix U hU hy hf
  have heq := hgap.hasDerivAt_eq_zero (hfirst.sub (hscalar.const_mul (2 * Real.sqrt b)))
  apply (eq_div_iff (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)).ne').mpr
  nlinarith [heq]

end PoincareConjecture.M14
