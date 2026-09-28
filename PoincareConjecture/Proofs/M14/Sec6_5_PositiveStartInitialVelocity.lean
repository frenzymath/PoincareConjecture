import PoincareConjecture.Proofs.M14.Sec6_2_SquareRootVelocityExtension










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

private theorem projection_heq {q r : G.Point} (h : q = r)
    {v : TangentSpace (spacetimeModel n) q} {w : TangentSpace (spacetimeModel n) r}
    (hv : HEq v w) :
    HEq (G.spacetime.horizontalProjection q v) (G.spacetime.horizontalProjection r w) := by
  cases h
  cases hv
  rfl

private theorem inner_heq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} {w : G.Horizontal r} (hv : HEq v w) :
    G.spacetime.horizontalMetric.inner q v v =
      G.spacetime.horizontalMetric.inner r w w := by
  cases h
  cases hv
  rfl




theorem positiveStart_initial_velocity_heq (R : M14SquareRootPath G p)
    (hp : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      p.curve (Icc a b) a)
    (hderiv : mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve (Icc a b) a 1 =
      -G.spacetime.timeVector (p.curve a) + (p.horizontal_velocity a).val) :
    HEq (R.horizontal_velocity (Real.sqrt a))
      ((2 * Real.sqrt a) • p.horizontal_velocity a) := by
  let C := M14SqrtParameterInterval a b
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hs : Real.sqrt a ∈ C := ⟨le_rfl, hab.le⟩
  have hC : UniqueDiffWithinAt ℝ C (Real.sqrt a) := uniqueDiffOn_Icc hab _ hs
  have hmaps : C ⊆ (fun r : ℝ => r ^ 2) ⁻¹' Icc a b := by
    intro r hr
    have hr0 := (Real.sqrt_nonneg a).trans hr.1
    constructor
    · nlinarith [Real.sq_sqrt p.tau_nonneg, Real.sqrt_nonneg a, hr.1]
    · nlinarith [Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le),
        Real.sqrt_nonneg b, hr.2]
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * Real.sqrt a) (Real.sqrt a) := by
    simpa using hasDerivAt_pow 2 (Real.sqrt a)
  have hdsq : mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2)
      C (Real.sqrt a) 1 = 2 * Real.sqrt a := by
    have h := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1)
      (mfderivWithin_eq_fderivWithin (𝕜 := ℝ) (f := fun r : ℝ => r ^ 2)
        (s := C) (x := Real.sqrt a))
    exact h.trans (hsq.hasDerivWithinAt.derivWithin hC)
  have hcomp := mfderivWithin_comp_of_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (I'' := spacetimeModel n) hp hsq.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
      hmaps hC.uniqueMDiffWithinAt (Real.sq_sqrt p.tau_nonneg)
  have heq := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
    R.agrees hs
  have hd : mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) R.curve C (Real.sqrt a) 1 =
      (2 * Real.sqrt a) •
        (-G.spacetime.timeVector (p.curve a) + (p.horizontal_velocity a).val) := by
    have h₁ := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1) heq
    have h₂ := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1) hcomp
    change mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => p.curve (r ^ 2))
      C (Real.sqrt a) 1 = mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve
        (Icc a b) a (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ => r ^ 2)
          C (Real.sqrt a) 1) at h₂
    rw [hdsq] at h₂
    apply h₁.trans (h₂.trans ?_)
    calc
      _ = (2 * Real.sqrt a) • mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
          p.curve (Icc a b) a 1 := by
        simpa only [smul_eq_mul, mul_one] using
          (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve (Icc a b) a).map_smul
            (2 * Real.sqrt a) 1
      _ = _ := by rw [hderiv]
  have hpoint : R.curve (Real.sqrt a) = p.curve a := by
    rw [R.agrees _ hs, Real.sq_sqrt p.tau_nonneg]
  rw [squareRoot_horizontalVelocity_eq_projection R hs]
  have hproj := projection_heq (G := G) hpoint (heq_of_eq hd)
  simpa only [map_smul, map_add, map_neg, horizontalProjection_timeVector_eq_zero,
    neg_zero, zero_add, G.spacetime.horizontalProjection_identity] using hproj




theorem positiveStart_initial_velocity_norm (R : M14SquareRootPath G p)
    (hp : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      p.curve (Icc a b) a)
    (hderiv : mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve (Icc a b) a 1 =
      -G.spacetime.timeVector (p.curve a) + (p.horizontal_velocity a).val) :
    G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt a))
        (R.horizontal_velocity (Real.sqrt a)) (R.horizontal_velocity (Real.sqrt a)) =
      4 * a * G.spacetime.horizontalMetric.inner (p.curve a)
        (p.horizontal_velocity a) (p.horizontal_velocity a) := by
  have hpoint : R.curve (Real.sqrt a) = p.curve a := by
    rw [R.agrees _ ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩,
      Real.sq_sqrt p.tau_nonneg]
  rw [inner_heq hpoint (positiveStart_initial_velocity_heq R hp hderiv)]
  simp only [map_smul, smul_apply, smul_eq_mul]
  calc
    _ = 4 * (Real.sqrt a) ^ 2 * G.spacetime.horizontalMetric.inner (p.curve a)
        (p.horizontal_velocity a) (p.horizontal_velocity a) := by ring
    _ = _ := by rw [Real.sq_sqrt p.tau_nonneg]

end PoincareConjecture.M14
