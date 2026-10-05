import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Differential.RectanglePartialTangent
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareRootVelocityExtension
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The actual square-root velocity of a variation

Morgan-Tian equations (6.1)-(6.2) and Lemma 6.4, pp. 106-108.
The actual within derivative is smooth on the closed rectangle. Its
identification with the supplied rescaled field is only asserted in the
interior, since the totalized original velocity does not prescribe the
square-root derivative at time zero.
-/

set_option autoImplicit false
-- Tangent fibers at different basepoints share the selected spacetime vector model.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

/-- The actual horizontal square-root velocity, including its within
endpoint values, for the nonsingular density in equation (6.2), p. 106. -/
noncomputable def variationSquareVelocity (V : M14LVariationData G p R) (s u : ℝ) :
    G.Horizontal (V.squareFamily s u) :=
  G.spacetime.horizontalProjection (V.squareFamily s u)
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily r u)
      (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ))

/-- The actual horizontal square-root velocity is smooth on the entire
closed-by-open variation rectangle, Lemma 6.4, pp. 107-108. -/
theorem variationSquareVelocity_smooth (V : M14LVariationData G p R) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × ℝ => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (V.squareFamily z.1 z.2) (variationSquareVelocity V z.1 z.2))
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain) := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have htan := (V.square_smooth.mono V.square_contains).contMDiffOn_partialTangentWithin_fst_prod
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)) hP.uniqueDiffOn
    (1 : ℝ) (k := ∞) (by simp)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  exact hproj.comp_contMDiffOn htan

/-- The supplied family derivative equation forces genuine interior
differentiability; its clock component cannot be a totalized zero
derivative, Definitions 6.1-6.2, pp. 105-106. -/
theorem variation_family_mdifferentiableAt (V : M14LVariationData G p R)
    {u τ : ℝ} (hu : u ∈ V.parameterDomain) (hτ : τ ∈ Set.Ioo τ₁ τ₂) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.family r u) τ := by
  by_contra hnot
  have hz := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1)
    (mfderiv_zero_of_not_mdifferentiableAt hnot)
  change mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.family r u) τ (1 : ℝ) = 0 at hz
  rw [V.family_derivative u hu τ hτ] at hz
  let dt : SpacetimeModelVector n →L[ℝ] ℝ :=
    mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (V.family τ u)
  have ht := congrArg dt hz
  have hc : dt (G.spacetime.timeVector (V.family τ u)) = 1 :=
    G.spacetime.timeVector_normalized (V.family τ u)
  have hv : dt (V.family_velocity u τ).val = 0 := (V.family_velocity u τ).property
  norm_num only [map_add, map_neg, map_zero, hc, hv, add_zero, neg_eq_zero, one_ne_zero] at ht

private theorem square_tangent (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hu : u ∈ V.parameterDomain) :
    mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily r u)
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ) =
      (2 * s) • mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
        (fun r => V.family r u) (s ^ 2) (1 : ℝ) := by
  have hs0 : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt hs.1
  have hτ : s ^ 2 ∈ Set.Ioo τ₁ τ₂ :=
    ⟨Real.lt_sq_of_sqrt_lt hs.1, (Real.lt_sqrt hs0.le).mp hs.2⟩
  have hnear : (fun r => V.squareFamily r u) =ᶠ[𝓝 s] fun r => V.family (r ^ 2) u :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2)
      (fun r hr => V.square_agrees r ⟨hr.1.le, hr.2.le⟩ u hu)
  have hg := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1)
    (hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n))
  have hw := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1)
    (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
      (f := fun r => V.squareFamily r u) (Icc_mem_nhds hs.1 hs.2))
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hsqmf : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2) s (1 : ℝ) = 2 * s := by
    have hm := hsq.hasFDerivAt.hasMFDerivAt.mfderiv
    have hv := congrArg (fun L : TangentSpace (𝓘(ℝ, ℝ)) s →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ)) (s ^ 2) => L 1) hm
    change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * s)) (1 : ℝ) at hv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hv
  have hinput : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2) s (1 : ℝ) =
      (2 * s) • (1 : TangentSpace (𝓘(ℝ, ℝ)) s) := by
    rw [hsqmf]
    simp
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ => r ^ 2)
    (g := fun r => V.family r u) (variation_family_mdifferentiableAt V hu hτ)
    hsq.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hinput, map_smul] at hchain
  exact hw.trans (hg.trans hchain)

private theorem horizontal_transport_val {q r : G.Point} (h : q = r)
    (v : G.Horizontal r) : (h.symm ▸ v : G.Horizontal q).val = v.val := by
  cases h
  rfl

/-- The actual square-root horizontal velocity equals the supplied
rescaled original velocity on the interior, equations (6.1)-(6.2), p. 106.
No endpoint agreement of these totalized fields is asserted. -/
theorem variationSquareVelocity_eq_rescaled (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hu : u ∈ V.parameterDomain) :
    variationSquareVelocity V s u =
      (V.square_agrees s ⟨hs.1.le, hs.2.le⟩ u hu).symm ▸
        ((2 * s) • V.family_velocity u (s ^ 2)) := by
  apply Subtype.ext
  rw [horizontal_transport_val (V.square_agrees s ⟨hs.1.le, hs.2.le⟩ u hu)]
  unfold variationSquareVelocity
  rw [square_tangent V hs hu, V.square_agrees s ⟨hs.1.le, hs.2.le⟩ u hu]
  have hs0 : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt hs.1
  rw [V.family_derivative u hu (s ^ 2)
    ⟨Real.lt_sq_of_sqrt_lt hs.1, (Real.lt_sqrt hs0.le).mp hs.2⟩,
    map_smul, map_add, map_neg, horizontalProjection_timeVector_eq_zero,
    neg_zero, zero_add, G.spacetime.horizontalProjection_identity]

end PoincareMT.M14
