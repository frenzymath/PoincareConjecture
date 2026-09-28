import PoincareConjecture.Statements.M13BackwardEndpoints
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Pointwise

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem backwardDomain_mapsTo (hQ : 0 < Q) (J : Set ℝ) :
    Set.MapsTo (fun s : ℝ ↦ s / Q) (parabolicBackwardDomain Q J) J := by
  rintro s ⟨t, ht, rfl⟩
  simpa [mul_div_cancel_left₀, hQ.ne'] using ht

theorem backwardDomain_uniqueDiff (hQ : 0 < Q) (J : Set ℝ) (s : ℝ)
    (hJ : UniqueDiffWithinAt ℝ J (s / Q)) :
    UniqueDiffWithinAt ℝ (parabolicBackwardDomain Q J) s := by
  have h := hJ.smul (c := Q) hQ.ne'
  change UniqueDiffWithinAt ℝ ((fun t : ℝ ↦ Q * t) '' J) (Q * (s / Q)) at h
  simpa [parabolicBackwardDomain, mul_div_cancel₀ _ hQ.ne'] using h

theorem backward_mdifferentiableWithinAt
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q)) :
    MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n)
      (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ)
      (parabolicBackwardDomain Q J) s := by
  have hc : MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ)
      (fun t : ℝ ↦ t / Q) (parabolicBackwardDomain Q J) s :=
    ((hasDerivAt_id s).div_const Q).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  have hg := hγ.comp s hc (backwardDomain_mapsTo hQ J)
  have hi := P.identification.mdifferentiable (by simp) (γ (s / Q))
  have hp := hi.comp_mdifferentiableWithinAt s hg
  exact hp.congr (fun t _ ↦ (P.identification_eq (γ (t / Q))).symm)
    (P.identification_eq (γ (s / Q))).symm

theorem backward_mfderivWithin
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ)
    (hJ : UniqueDiffWithinAt ℝ J (s / Q))
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q)) :
    (show SpacetimeModelVector n from
      mfderivWithin 𝓘(ℝ) (spacetimeModel n)
        (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ)
        (parabolicBackwardDomain Q J) s (1 : ℝ)) =
      (1 / Q : ℝ) • (mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) (1 : ℝ)) := by
  have hc : HasMFDerivWithinAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ ↦ t / Q)
      (parabolicBackwardDomain Q J) s
      (ContinuousLinearMap.toSpanSingleton ℝ (1 / Q : ℝ)) := by
    simpa using ((hasDerivAt_id s).div_const Q).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hg := hγ.hasMFDerivWithinAt.comp s hc (backwardDomain_mapsTo hQ J)
  have hi := P.identification.mdifferentiable (by simp) (γ (s / Q))
  have hp := hi.hasMFDerivAt.comp_hasMFDerivWithinAt s hg
  have heq := hp.mfderivWithin (backwardDomain_uniqueDiff hQ J s hJ).uniqueMDiffWithinAt
  have heq' : (show ℝ →L[ℝ] SpacetimeModelVector n from
      mfderivWithin 𝓘(ℝ) (spacetimeModel n)
        (P.identification ∘ (γ ∘ (fun t : ℝ ↦ t / Q)))
        (parabolicBackwardDomain Q J) s) =
      (show SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n from
        mfderiv (spacetimeModel n) (spacetimeModel n) P.identification (γ (s / Q))).comp
      ((show ℝ →L[ℝ] SpacetimeModelVector n from
        mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J (s / Q)).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (1 / Q : ℝ))) := heq
  have hfun : (P.identification ∘ (γ ∘ (fun t : ℝ ↦ t / Q))) =
      (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ) := by
    funext t
    exact P.identification_eq (γ (t / Q))
  rw [hfun] at heq'
  have hv := congrArg (fun f : ℝ →L[ℝ] SpacetimeModelVector n ↦ f 1) heq'
  have heval : (show SpacetimeModelVector n from
      mfderivWithin 𝓘(ℝ) (spacetimeModel n)
        (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ)
        (parabolicBackwardDomain Q J) s (1 : ℝ)) =
      mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) (1 / Q : ℝ) := by
    exact (hv.trans (by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one]
      exact P.differential_eq _ _))
  rw [heval]
  have hc1 : (show TangentSpace 𝓘(ℝ) (s / Q) from (1 / Q : ℝ)) =
      (1 / Q : ℝ) • (show TangentSpace 𝓘(ℝ) (s / Q) from (1 : ℝ)) := by
    change (1 / Q : ℝ) = (1 / Q) * 1
    rw [mul_one]
  exact (congrArg (fun v : TangentSpace 𝓘(ℝ) (s / Q) ↦
    mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) v) hc1).trans
    ((mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J (s / Q)).map_smul _ _)

theorem backward_velocityWithin_val
    (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (τ : ℝ)
    (hJ : UniqueDiffWithinAt ℝ J τ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J τ)
    (ht : HasDerivWithinAt (fun s ↦ R.spacetime.timeFunction (γ s)) (-1) J τ) :
    (backwardHorizontalVelocityWithin R.spacetime γ J τ).val =
      mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J τ (1 : ℝ) +
        R.spacetime.timeVector (γ τ) := by
  have hsmooth : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ R.spacetime.timeFunction :=
    R.spacetime.time_smooth
  have htime : MDifferentiable (spacetimeModel n) 𝓘(ℝ) R.spacetime.timeFunction :=
    hsmooth.mdifferentiable (by simp)
  have hc := mfderiv_comp_mfderivWithin τ (htime (γ τ)) hγ hJ.uniqueMDiffWithinAt
  have hc' : (show ℝ →L[ℝ] ℝ from
      mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (R.spacetime.timeFunction ∘ γ) J τ) =
      (show SpacetimeModelVector n →L[ℝ] ℝ from
        mfderiv (spacetimeModel n) 𝓘(ℝ) R.spacetime.timeFunction (γ τ)).comp
      (show ℝ →L[ℝ] SpacetimeModelVector n from
        mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J τ) := hc
  have ht' : (show ℝ →L[ℝ] ℝ from
      mfderivWithin 𝓘(ℝ) 𝓘(ℝ)
        (fun s ↦ R.spacetime.timeFunction (γ s)) J τ) =
      ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ) :=
    ht.hasFDerivWithinAt.hasMFDerivWithinAt.mfderivWithin hJ.uniqueMDiffWithinAt
  let V : TangentSpace (spacetimeModel n) (γ τ) :=
    mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J τ (1 : ℝ)
  let dt : TangentSpace (spacetimeModel n) (γ τ) →L[ℝ] ℝ :=
    mfderiv (spacetimeModel n) 𝓘(ℝ) R.spacetime.timeFunction (γ τ)
  have hclock : dt V = -1 := by
    exact (congrArg (fun f : ℝ →L[ℝ] ℝ ↦ f 1) (hc'.symm.trans ht')).trans
      (ContinuousLinearMap.toSpanSingleton_apply_one ℝ (-1 : ℝ))
  have hproj : (backwardHorizontalVelocityWithin R.spacetime γ J τ).val =
      V - dt V • R.spacetime.timeVector (γ τ) :=
    R.spacetime.horizontalProjection_eq _ _
  rw [hproj, hclock]
  simp [V]

theorem backward_velocityWithin
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ)
    (hJ : UniqueDiffWithinAt ℝ J (s / Q))
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q)) :
    backwardHorizontalVelocityWithin P.realization.spacetime (parabolicBackwardCurve Q γ)
      (parabolicBackwardDomain Q J) s =
      (1 / Q : ℝ) • P.horizontal (γ (s / Q))
        (backwardHorizontalVelocityWithin R.spacetime γ J (s / Q)) := by
  have hd := backward_mfderivWithin P γ J s hJ hγ
  have hp := congrArg
    (show SpacetimeModelVector n → P.realization.spacetime.Horizontal (γ (s / Q)) from
      P.realization.spacetime.horizontalProjection (γ (s / Q))) hd
  change backwardHorizontalVelocityWithin P.realization.spacetime (parabolicBackwardCurve Q γ)
    (parabolicBackwardDomain Q J) s = _ at hp
  rw [hp]
  change P.realization.spacetime.horizontalProjection (γ (s / Q))
      ((1 / Q : ℝ) • (show TangentSpace (spacetimeModel n)
          (show P.realization.spacetime.Point from γ (s / Q)) from
        mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) (1 : ℝ))) = _
  rw [map_smul, P.projection_eq]
  rfl

theorem backward_energyWithin
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ)
    (hJ : UniqueDiffWithinAt ℝ J (s / Q))
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q)) :
    P.realization.spacetime.horizontalMetric.inner (γ (s / Q))
      (backwardHorizontalVelocityWithin P.realization.spacetime (parabolicBackwardCurve Q γ)
        (parabolicBackwardDomain Q J) s)
      (backwardHorizontalVelocityWithin P.realization.spacetime (parabolicBackwardCurve Q γ)
        (parabolicBackwardDomain Q J) s) =
      R.spacetime.horizontalMetric.inner (γ (s / Q))
        (backwardHorizontalVelocityWithin R.spacetime γ J (s / Q))
        (backwardHorizontalVelocityWithin R.spacetime γ J (s / Q)) / Q := by
  rw [backward_velocityWithin P γ J s hJ hγ]
  simp only [map_smul, smul_apply, smul_eq_mul, P.metric_eq]
  field_simp [hQ.ne']

theorem parabolicBackwardEndpointCalculus
    (P : ParabolicSpacetimeRescaling R Q hQ a) : ParabolicBackwardEndpointCalculus P where
  differentiable := backward_mdifferentiableWithinAt P
  derivative := backward_mfderivWithin P
  velocity_val := backward_velocityWithin_val
  velocity := backward_velocityWithin P
  energy := backward_energyWithin P

theorem backwardDomain_univ (hQ : 0 < Q) :
    parabolicBackwardDomain Q (Set.univ : Set ℝ) = Set.univ := by
  ext s
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨s / Q, trivial, mul_div_cancel₀ s hQ.ne'⟩

theorem backward_time
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (T : ℝ)
    (ht : ∀ τ ∈ J, R.spacetime.timeFunction (γ τ) = T - τ)
    (s : ℝ) (hs : s / Q ∈ J) :
    P.realization.spacetime.timeFunction (parabolicBackwardCurve Q γ s) =
      parabolicTime Q a T - s := by
  change P.atlasRescaling.atlas.time (γ (s / Q)) = parabolicTime Q a T - s
  rw [P.atlasRescaling.time_eq]
  change parabolicTime Q a (R.spacetime.timeFunction (γ (s / Q))) =
    parabolicTime Q a T - s
  rw [ht (s / Q) hs]
  unfold parabolicTime
  field_simp [hQ.ne']
  ring

theorem backward_mfderiv
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (s : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ (s / Q)) :
    (show SpacetimeModelVector n from
      mfderiv 𝓘(ℝ) (spacetimeModel n)
        (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ)
        s (1 : ℝ)) =
      (1 / Q : ℝ) • (mfderiv 𝓘(ℝ) (spacetimeModel n) γ (s / Q) (1 : ℝ)) := by
  simpa only [backwardDomain_univ hQ, mfderivWithin_univ] using
    backward_mfderivWithin P γ Set.univ s uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt

theorem backward_velocity_val
    (γ : ℝ → R.spacetime.Point) (τ : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ τ)
    (ht : HasDerivAt (fun s ↦ R.spacetime.timeFunction (γ s)) (-1) τ) :
    (backwardHorizontalVelocity R.spacetime γ τ).val =
      mfderiv 𝓘(ℝ) (spacetimeModel n) γ τ (1 : ℝ) + R.spacetime.timeVector (γ τ) := by
  simpa only [backwardHorizontalVelocityWithin, backwardHorizontalVelocity,
    mfderivWithin_univ] using
    backward_velocityWithin_val γ Set.univ τ uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt ht.hasDerivWithinAt

theorem backward_velocity
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (s : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ (s / Q)) :
    backwardHorizontalVelocity P.realization.spacetime (parabolicBackwardCurve Q γ) s =
      (1 / Q : ℝ) • P.horizontal (γ (s / Q))
        (backwardHorizontalVelocity R.spacetime γ (s / Q)) := by
  simpa only [backwardDomain_univ hQ, backwardHorizontalVelocityWithin,
    backwardHorizontalVelocity, mfderivWithin_univ] using
    backward_velocityWithin P γ Set.univ s uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt

theorem backward_energy
    (P : ParabolicSpacetimeRescaling R Q hQ a)
    (γ : ℝ → R.spacetime.Point) (s : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ (s / Q)) :
    P.realization.spacetime.horizontalMetric.inner (γ (s / Q))
      (backwardHorizontalVelocity P.realization.spacetime (parabolicBackwardCurve Q γ) s)
      (backwardHorizontalVelocity P.realization.spacetime (parabolicBackwardCurve Q γ) s) =
      R.spacetime.horizontalMetric.inner (γ (s / Q))
        (backwardHorizontalVelocity R.spacetime γ (s / Q))
        (backwardHorizontalVelocity R.spacetime γ (s / Q)) / Q := by
  simpa only [backwardDomain_univ hQ, backwardHorizontalVelocityWithin,
    backwardHorizontalVelocity, mfderivWithin_univ] using
    backward_energyWithin P γ Set.univ s uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt

end PoincareConjecture.M13
