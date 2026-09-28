import PoincareConjecture.Proofs.M14.Sec6_2_VariationAction
import PoincareConjecture.Proofs.M14.Sec6_1_SquareRootAction










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

private theorem parameterDomain_isOpen (V : M14LVariationData G p R) :
    IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo



theorem variation_squareFamily_time (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hu : u ∈ V.parameterDomain) :
    G.spacetime.timeFunction (V.squareFamily s u) = T - s ^ 2 := by
  rw [V.square_agrees s hs u hu]
  apply V.family_time u hu
  have hs0 := (Real.sqrt_nonneg τ₁).trans hs.1
  constructor
  · nlinarith [Real.sq_sqrt p.tau_nonneg, Real.sqrt_nonneg τ₁, hs.1]
  · nlinarith [Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), hs.2,
      Real.sqrt_nonneg τ₂]



theorem variation_parameter_smooth (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞
      (fun u => V.squareFamily s u) V.parameterDomain :=
  (V.square_smooth.mono V.square_contains).comp
    ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn (fun _ hu => ⟨hs, hu⟩)



theorem variation_parameter_clock_eq_zero (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hu : u ∈ V.parameterDomain) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
      (V.squareFamily s u)
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily s r) u (1 : ℝ))) = 0 := by
  have hγ := ((variation_parameter_smooth V hs u hu).contMDiffAt
    ((parameterDomain_isOpen V).mem_nhds hu)).mdifferentiableAt (by simp)
  have htime : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have ht := (htime.mdifferentiable (by simp)
    (V.squareFamily s u)).hasMFDerivAt.comp u hγ.hasMFDerivAt
  have hd := ht.hasFDerivAt.hasDerivAt
  have hc : HasDerivAt (fun r => G.spacetime.timeFunction (V.squareFamily s r)) 0 u := by
    apply (hasDerivAt_const u (T - s ^ 2)).congr_of_eventuallyEq
    filter_upwards [(parameterDomain_isOpen V).mem_nhds hu] with r hr
    exact variation_squareFamily_time V hs hr
  exact hd.unique hc



theorem endpointVariationField_val_eq_tangent (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hu : u ∈ V.parameterDomain) :
    (M14EndpointVariationField V s u).val =
      mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily s r) u (1 : ℝ) := by
  let v : TangentSpace (spacetimeModel n) (V.squareFamily s u) :=
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily s r) u (1 : ℝ)
  change (G.spacetime.horizontalProjection (V.squareFamily s u) v).val = v
  rw [G.spacetime.horizontalProjection_eq]
  change v - (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
    (V.squareFamily s u) v) • G.spacetime.timeVector (V.squareFamily s u) = v
  rw [show (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
    (V.squareFamily s u) v) = 0 from variation_parameter_clock_eq_zero V hs hu,
    zero_smul, sub_zero]



theorem variation_square_tangent_clock (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hu : u ∈ V.parameterDomain) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
      (V.squareFamily s u)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily r u)
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ))) = -(2 * s) := by
  have hγ := (V.square_smooth.mono V.square_contains).comp
    (contMDiff_id.prodMk (contMDiff_const (c := u))).contMDiffOn (fun _ hr => ⟨hr, hu⟩)
  have htime : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have ht := (htime.mdifferentiable (by simp)
    (V.squareFamily s u)).hasMFDerivAt.comp_hasMFDerivWithinAt s
      ((hγ s hs).mdifferentiableWithinAt (by simp)).hasMFDerivWithinAt
  have hd := ht.hasFDerivWithinAt.hasDerivWithinAt
  have hc : HasDerivWithinAt (fun r => G.spacetime.timeFunction (V.squareFamily r u))
      (-(2 * s)) (M14SqrtParameterInterval τ₁ τ₂) s := by
    have hpoly : HasDerivAt (fun r : ℝ => T - r ^ 2) (-(2 * s)) s := by
      convert! (hasDerivAt_const s T).sub (hasDerivAt_pow 2 s) using 1
      simp
    exact hpoly.hasDerivWithinAt.congr_of_mem (fun r hr => variation_squareFamily_time V hr hu) hs
  have hJ := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hs
  exact (hd.derivWithin hJ).symm.trans (hc.derivWithin hJ)



theorem variationSquareVelocity_val_eq_tangent_add_time (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hu : u ∈ V.parameterDomain) :
    (variationSquareVelocity V s u).val =
      mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily r u)
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ) +
      (2 * s) • G.spacetime.timeVector (V.squareFamily s u) := by
  let v : TangentSpace (spacetimeModel n) (V.squareFamily s u) :=
    mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily r u)
      (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ)
  change (G.spacetime.horizontalProjection (V.squareFamily s u) v).val =
    v + (2 * s) • G.spacetime.timeVector (V.squareFamily s u)
  rw [G.spacetime.horizontalProjection_eq]
  change v - (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
    (V.squareFamily s u) v) • G.spacetime.timeVector (V.squareFamily s u) = _
  rw [show (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction
    (V.squareFamily s u) v) = -(2 * s) from variation_square_tangent_clock V hs hu,
    neg_smul, sub_neg_eq_add]

private theorem horizontal_transport_val {q r : G.Point} (h : q = r)
    (v : G.Horizontal r) : (h.symm ▸ v : G.Horizontal q).val = v.val := by
  cases h
  rfl




theorem variationSquareVelocity_zero (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    variationSquareVelocity V s 0 = (V.square_base s).symm ▸ R.horizontal_velocity s := by
  apply Subtype.ext
  rw [horizontal_transport_val (V.square_base s)]
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
    (fun r (_ : r ∈ M14SqrtParameterInterval τ₁ τ₂) => V.square_base r) hs
  have hv := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1) hd
  unfold variationSquareVelocity
  erw [hv, V.square_base s]
  exact congrArg Subtype.val (squareRoot_horizontalVelocity_eq_projection R hs).symm

private theorem inner_transport {q r : G.Point} (h : q = r) (v w : G.Horizontal r) :
    G.spacetime.horizontalMetric.inner q (h.symm ▸ v) (h.symm ▸ w) =
      G.spacetime.horizontalMetric.inner r v w := by
  cases h
  rfl



theorem variationActionDensity_zero (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    variationActionDensity V (s, 0) = squareRootLIntegrand R s := by
  unfold variationActionDensity squareRootLIntegrand
  rw [variationSquareVelocity_zero V hs, inner_transport (V.square_base s), V.square_base s]

end PoincareConjecture.M14
