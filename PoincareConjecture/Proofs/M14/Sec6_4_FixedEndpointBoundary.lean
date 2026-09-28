import PoincareConjecture.Proofs.M14.Sec6_2_PullbackZero
import PoincareConjecture.Statements.M14PathCalculus










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

private theorem parameterDomain_isOpen (V : M14LVariationData G p R) :
    IsOpen V.parameterDomain := by
  rw [V.parameterDomain_eq]
  exact isOpen_Ioo

private theorem zero_mem_parameterDomain (V : M14LVariationData G p R) :
    (0 : ℝ) ∈ V.parameterDomain := by
  rw [V.parameterDomain_eq]
  exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩

private theorem horizontal_transport_zero {q r : G.Point} (h : q = r) :
    (h.symm ▸ (0 : G.Horizontal q) : G.Horizontal r) = 0 := by
  cases h
  rfl



theorem endpointVariationField_eq_zero_of_constant (V : M14LVariationData G p R)
    {s : ℝ}
    (hfix : Set.EqOn (V.squareFamily s) (fun _ => V.squareFamily s 0) V.parameterDomain)
    {u : ℝ} (hu : u ∈ V.parameterDomain) : M14EndpointVariationField V s u = 0 := by
  have hg : V.squareFamily s =ᶠ[𝓝 u] (fun _ => V.squareFamily s 0) :=
    Filter.eventually_of_mem ((parameterDomain_isOpen V).mem_nhds hu) (fun _ hr => hfix hr)
  have hd : (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (V.squareFamily s) u :
      ℝ →L[ℝ] SpacetimeModelVector n) = 0 :=
    (hg.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)).trans mfderiv_const
  have hv : mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (V.squareFamily s) u (1 : ℝ) =
      (0 : TangentSpace (spacetimeModel n) (V.squareFamily s u)) :=
    congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1) hd
  simp only [M14EndpointVariationField, hv, map_zero]
  rfl



theorem variationField_eq_zero_of_constant (V : M14LVariationData G p R)
    {s : ℝ}
    (hfix : Set.EqOn (V.squareFamily s) (fun _ => V.squareFamily s 0) V.parameterDomain) :
    M14VariationField V s = 0 := by
  change (V.square_base s).symm ▸ M14EndpointVariationField V s 0 = 0
  rw [endpointVariationField_eq_zero_of_constant V hfix (zero_mem_parameterDomain V)]
  exact horizontal_transport_zero (V.square_base s)



theorem variationEndpointAcceleration_eq_zero_of_constant (V : M14LVariationData G p R)
    (D : M14VariationDerivativeData V) {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hfix : Set.EqOn (V.squareFamily s) (fun _ => V.squareFamily s 0) V.parameterDomain) :
    M14VariationEndpointAcceleration V D s hs = 0 := by
  have h0 := zero_mem_parameterDomain V
  have hc := horizontalCovariantDerivative_eq_zero_of_constant (D.endpoint_extension s hs)
    h0 ((parameterDomain_isOpen V).uniqueDiffOn 0 h0) hfix
      (fun _ hu => endpointVariationField_eq_zero_of_constant V hfix hu)
  unfold M14VariationEndpointAcceleration
  rw [hc]
  exact horizontal_transport_zero (V.square_base s)

private theorem square_fixed_of_endpoint (V : M14LVariationData G p R)
    {τ : ℝ} (hτ : 0 ≤ τ) (hs : Real.sqrt τ ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hfix : ∀ u ∈ V.parameterDomain, V.family τ u = p.curve τ) :
    Set.EqOn (V.squareFamily (Real.sqrt τ))
      (fun _ => V.squareFamily (Real.sqrt τ) 0) V.parameterDomain := by
  have heq (u : ℝ) (hu : u ∈ V.parameterDomain) :
      V.squareFamily (Real.sqrt τ) u = p.curve τ := by
    rw [V.square_agrees _ hs u hu, Real.sq_sqrt hτ]
    exact hfix u hu
  intro u hu
  exact (heq u hu).trans (heq 0 (zero_mem_parameterDomain V)).symm

private theorem fixed_square_endpoints (V : M14LVariationData G p R)
    (hfix : M14BothEndpointsFixed V) :
    Set.EqOn (V.squareFamily (Real.sqrt τ₁))
        (fun _ => V.squareFamily (Real.sqrt τ₁) 0) V.parameterDomain ∧
      Set.EqOn (V.squareFamily (Real.sqrt τ₂))
        (fun _ => V.squareFamily (Real.sqrt τ₂) 0) V.parameterDomain := by
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  exact ⟨square_fixed_of_endpoint V p.tau_nonneg ⟨le_rfl, hle⟩
      (V.left_endpoint_fixed_spec.mp hfix.1),
    square_fixed_of_endpoint V (p.tau_nonneg.trans p.tau_lt.le) ⟨hle, le_rfl⟩
      (V.right_endpoint_fixed_spec.mp hfix.2)⟩



theorem firstVariationBoundaryTerm_eq_zero (V : M14LVariationData G p R)
    (hfix : M14BothEndpointsFixed V) : M14FirstVariationBoundaryTerm V = 0 := by
  obtain ⟨hl, hr⟩ := fixed_square_endpoints V hfix
  simp only [M14FirstVariationBoundaryTerm, variationField_eq_zero_of_constant V hl,
    variationField_eq_zero_of_constant V hr, map_zero, sub_self]



theorem variationField_fixed_endpoints_eq_zero (V : M14LVariationData G p R)
    (hfix : M14BothEndpointsFixed V) :
    M14VariationField V (Real.sqrt τ₁) = 0 ∧ M14VariationField V (Real.sqrt τ₂) = 0 := by
  obtain ⟨hl, hr⟩ := fixed_square_endpoints V hfix
  exact ⟨variationField_eq_zero_of_constant V hl, variationField_eq_zero_of_constant V hr⟩



theorem secondVariationBoundaryTerm_eq_zero (V : M14LVariationData G p R)
    (D : M14VariationDerivativeData V) (hfix : M14BothEndpointsFixed V) :
    M14SecondVariationBoundaryTerm V D = 0 := by
  obtain ⟨hl, hr⟩ := fixed_square_endpoints V hfix
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have hleft := variationEndpointAcceleration_eq_zero_of_constant V D ⟨le_rfl, hle⟩ hl
  have hright := variationEndpointAcceleration_eq_zero_of_constant V D ⟨hle, le_rfl⟩ hr
  simp only [M14SecondVariationBoundaryTerm, hleft, hright, map_zero, sub_self]

end PoincareConjecture.M14
