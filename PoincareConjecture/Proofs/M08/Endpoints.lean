import PoincareConjecture.Proofs.M08.PathCongruence








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]


theorem squareFamily_left_eq {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : InitialFixedLVariation F T τ₁ τ₂ p) {u : ℝ}
    (hu : u ∈ V.toLVariation.parameterDomain) :
    V.squareFamily (Real.sqrt τ₁) u = p.curve τ₁ := by
  rw [V.square_agrees (Real.sqrt τ₁)
    ⟨le_rfl, Real.sqrt_le_sqrt p.ordered.le⟩ u hu, Real.sq_sqrt p.nonnegative]
  exact V.fixed_left u hu


theorem squareFamily_right_eq {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) {u : ℝ}
    (hu : u ∈ V.toLVariation.parameterDomain) :
    V.squareFamily (Real.sqrt τ₂) u = p.curve τ₂ := by
  rw [V.square_agrees (Real.sqrt τ₂)
    ⟨Real.sqrt_le_sqrt p.ordered.le, le_rfl⟩ u hu,
    Real.sq_sqrt (p.nonnegative.trans p.ordered.le)]
  exact V.fixed_right u hu


theorem squareVariationField_eq_zero_of_constant {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (s : ℝ) (x : M)
    (hfixed : ∀ u ∈ V.parameterDomain, V.squareFamily s u = x) :
    squareVariationField V s = 0 := by
  exact curveVelocity_eq_zero_of_eventually_constant
    (Filter.eventually_of_mem
      (isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩) hfixed)


theorem variationEndpointAcceleration_eq_zero_of_constant
    {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) (x : M)
    (hfixed : ∀ u ∈ V.parameterDomain, V.squareFamily s u = x) :
    variationEndpointAcceleration V D s hs = 0 := by
  let E := D.endpoint_extension s hs
  have hzero : (0 : ℝ) ∈ V.parameterDomain :=
    ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hvelocity (u : ℝ) (hu : u ∈ V.parameterDomain) :
      curveVelocityWithin (n := n) (V.squareFamily s) V.parameterDomain u = 0 :=
    curveVelocityWithin_eq_zero_of_constant hfixed hu
  have hagrees (u : ℝ) (hu : u ∈ V.parameterDomain) :
      E.extension u (V.squareFamily s 0) = 0 := by
    have hbase : V.squareFamily s u = V.squareFamily s 0 :=
      (hfixed u hu).trans (hfixed 0 hzero).symm
    rw [← hbase]
    exact (E.agrees u hu).trans (hvelocity u hu)
  have hnear : (fun u ↦ E.extension u (V.squareFamily s 0)) =ᶠ[𝓝 (0 : ℝ)]
      fun _ ↦ 0 :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hzero) hagrees
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  have hderiv : deriv (fun u ↦ E.extension u (V.squareFamily s 0)) 0 = 0 := by
    rw [hnear.deriv_eq]
    simp
  change deriv (fun u ↦ E.extension u (V.squareFamily s 0)) 0 +
    (F.connection (T - s ^ 2)).connection (E.extension 0) (V.squareFamily s 0)
      (curveVelocityWithin (n := n) (V.squareFamily s) V.parameterDomain 0) = 0
  rw [hderiv, hvelocity 0 hzero]
  simp


theorem firstVariationBoundaryTerm_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) :
    firstVariationBoundaryTerm V.toLVariation = 0 := by
  have hleft := squareVariationField_eq_zero_of_constant V.toLVariation
    (Real.sqrt τ₁) (p.curve τ₁)
    (fun _ hu ↦ squareFamily_left_eq V.toInitialFixedLVariation hu)
  have hright := squareVariationField_eq_zero_of_constant V.toLVariation
    (Real.sqrt τ₂) (p.curve τ₂) (fun _ hu ↦ squareFamily_right_eq V hu)
  simp only [firstVariationBoundaryTerm, hleft, hright, map_zero, sub_self]


theorem secondVariationBoundaryTerm_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : FixedEndpointLVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V.toLVariation) :
    secondVariationBoundaryTerm V.toLVariation D = 0 := by
  have hleft := variationEndpointAcceleration_eq_zero_of_constant V.toLVariation D
    (Real.sqrt τ₁) ⟨le_rfl, Real.sqrt_le_sqrt p.ordered.le⟩ (p.curve τ₁)
    (fun _ hu ↦ squareFamily_left_eq V.toInitialFixedLVariation hu)
  have hright := variationEndpointAcceleration_eq_zero_of_constant V.toLVariation D
    (Real.sqrt τ₂) ⟨Real.sqrt_le_sqrt p.ordered.le, le_rfl⟩ (p.curve τ₂)
    (fun _ hu ↦ squareFamily_right_eq V hu)
  simp only [secondVariationBoundaryTerm, hleft, hright, map_zero, sub_self]

end PoincareConjecture.M08
