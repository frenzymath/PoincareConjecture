import PoincareConjecture.Proofs.M14.Mathlib.WithinVelocitySmooth
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedFieldExtension










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}



theorem horizontalProjection_timeVector_eq_zero (q : G.Point) :
    G.spacetime.horizontalProjection q (G.spacetime.timeVector q) = 0 := by
  apply Subtype.ext
  change (G.spacetime.horizontalProjection q (G.spacetime.timeVector q)).val = 0
  rw [G.spacetime.horizontalProjection_eq]
  have htime : (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction q
      (G.spacetime.timeVector q)) = (1 : ℝ) := G.spacetime.timeVector_normalized q
  change G.spacetime.timeVector q -
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction q
      (G.spacetime.timeVector q)) • G.spacetime.timeVector q = 0
  rw [htime, one_smul, sub_self]



theorem squareRoot_horizontalVelocity_eq_projection (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    R.horizontal_velocity s = G.spacetime.horizontalProjection (R.curve s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) R.curve
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ)) := by
  rw [R.derivative_eq s hs, map_add, map_smul,
    horizontalProjection_timeVector_eq_zero, smul_zero, zero_add]
  exact (G.spacetime.horizontalProjection_identity (R.curve s)
    (R.horizontal_velocity s)).symm



theorem squareRoot_horizontalVelocity_smooth (R : M14SquareRootPath G p) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (R.curve s) (R.horizontal_velocity s))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  have hinterval : Real.sqrt τ₁ < Real.sqrt τ₂ :=
    Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hv := (R.smooth.mono R.interval_subset).contMDiffOn_mfderivWithin_const_apply
    (uniqueDiffOn_Icc hinterval) (1 : ℝ) (k := ∞) (by simp)
  have hp : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj
          (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  have hproj := hp.comp_contMDiffOn hv
  apply hproj.congr
  intro s hs
  exact congrArg (fun v : G.Horizontal (R.curve s) =>
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) v)
      (squareRoot_horizontalVelocity_eq_projection R hs)




theorem exists_squareRoot_velocity_extension (R : M14SquareRootPath G p) :
    Nonempty (M14PullbackExtension G R.curve
      (M14SqrtParameterInterval τ₁ τ₂) R.horizontal_velocity) :=
  exists_pullbackExtension_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
    (squareRoot_horizontalVelocity_smooth R)

end PoincareConjecture.M14
