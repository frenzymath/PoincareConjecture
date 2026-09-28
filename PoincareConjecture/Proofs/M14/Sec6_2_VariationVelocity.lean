import PoincareConjecture.Proofs.M14.Mathlib.RectanglePartialTangent
import PoincareConjecture.Proofs.M14.Sec6_2_SquareRootVelocityExtension
import Mathlib.Analysis.Calculus.Deriv.Pow











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}



noncomputable def variationSquareVelocity (V : M14LVariationData G p R) (s u : ℝ) :
    G.Horizontal (V.squareFamily s u) :=
  G.spacetime.horizontalProjection (V.squareFamily s u)
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => V.squareFamily r u)
      (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ))



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

end PoincareConjecture.M14
