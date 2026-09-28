import PoincareConjecture.Proofs.M62.Sec19_1_PullbackAlgebra
import PoincareConjecture.Proofs.M09.VelocityChainRules
import PoincareConjecture.Definitions.M63Ramp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {a b : ℝ}

theorem curveVelocity_comp {gamma : ℝ → M} {phi : ℝ → ℝ} {x v : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x))
    (hphi : HasDerivAt phi v x) :
    curveVelocity (n := n) (fun y => gamma (phi y)) x =
      v • curveVelocity (n := n) gamma (phi x) := by
  have hvalue : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) phi x 1 = v := by
    rw [mfderiv_eq_fderiv, hphi.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ v
  have hcomp := mfderiv_comp_apply (f := phi) (g := gamma) x hgamma
    hphi.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (1 : ℝ)
  exact hcomp.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x)) hvalue).trans (by
    simpa only [curveVelocity, smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x)).map_smul v (1 : ℝ)))

variable [IsManifold (𝓡 n) ∞ M]

theorem curveSpeed_comp_abs (F : RicciFlow n M (Set.Icc a b))
    (d : ℝ → ℝ → M) {phi : ℝ → ℝ} {t x v : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t) (phi x))
    (hphi : HasDerivAt phi v x) :
    curveSpeed F (fun y s => d (phi y) s) t x = |v| * curveSpeed F d t (phi x) := by
  unfold curveSpeed RiemannianMetric.tangentNorm
  rw [curveVelocity_comp hd hphi]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq_eq_abs]

theorem curveSpeed_comp (F : RicciFlow n M (Set.Icc a b))
    (d : ℝ → ℝ → M) {phi : ℝ → ℝ} {t x v : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t) (phi x))
    (hphi : HasDerivAt phi v x) (hv : 0 ≤ v) :
    curveSpeed F (fun y s => d (phi y) s) t x = v * curveSpeed F d t (phi x) := by
  rw [curveSpeed_comp_abs F d hd hphi, abs_of_nonneg hv]

theorem spatialUnitTangent_comp (F : RicciFlow n M (Set.Icc a b))
    (d : ℝ → ℝ → M) {phi : ℝ → ℝ} {t x v : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t) (phi x))
    (hphi : HasDerivAt phi v x) (hv : 0 < v) :
    spatialUnitTangent F (fun y s => d (phi y) s) t x =
      spatialUnitTangent F d t (phi x) := by
  unfold spatialUnitTangent
  rw [curveSpeed_comp F d hd hphi hv.le, curveVelocity_comp hd hphi,
    mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hv.ne', mul_one]

theorem pullback_comp {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {gamma : ℝ → M} {Y : (y : ℝ) → TangentSpace (𝓡 n) (gamma y)}
    {phi : ℝ → ℝ} {x v : ℝ}
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨gamma y, Y y⟩ : TangentBundle (𝓡 n) M)) (phi x))
    (hphi : HasDerivAt phi v x) :
    rampHorizontalCovariantDerivative D (fun y => gamma (phi y)) (fun y => Y (phi y)) x =
      v • rampHorizontalCovariantDerivative D gamma Y (phi x) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    (gamma (phi x))
  let f : ℝ → EuclideanSpace ℝ (Fin n) := fun y => (e ⟨gamma y, Y y⟩).2
  rw [mdifferentiableAt_totalSpace] at hY
  have hf : DifferentiableAt ℝ f (phi x) := hY.2.differentiableAt
  change e.symmL ℝ (gamma (phi x)) (deriv (f ∘ phi) x) +
      D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y (phi x)))
        (gamma (phi x)) (curveVelocity (fun y => gamma (phi y)) x) =
    v • (e.symmL ℝ (gamma (phi x)) (deriv f (phi x)) +
      D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y (phi x)))
        (gamma (phi x)) (curveVelocity gamma (phi x)))
  rw [(hf.hasDerivAt.scomp x hphi).deriv, curveVelocity_comp hY.1 hphi,
    map_smul, map_smul, smul_add]

theorem spatialDerivative_comp (F : RicciFlow n M (Set.Icc a b))
    (d : ℝ → ℝ → M) {t : ℝ}
    {Y : (y : ℝ) → TangentSpace (𝓡 n) (d y t)} {phi : ℝ → ℝ} {x v : ℝ}
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, Y y⟩ : TangentBundle (𝓡 n) M)) (phi x))
    (hphi : HasDerivAt phi v x) (hv : 0 < v) :
    m62SpatialDerivative F (fun y s => d (phi y) s) t (fun y => Y (phi y)) x =
      m62SpatialDerivative F d t Y (phi x) := by
  have hcoords := hY
  rw [mdifferentiableAt_totalSpace] at hcoords
  have hd := hcoords.1
  unfold m62SpatialDerivative
  rw [curveSpeed_comp F d hd hphi hv.le, pullback_comp (F.connection t) hY hphi,
    mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hv.ne', mul_one]

theorem curvatureVector_comp (F : RicciFlow n M (Set.Icc a b))
    (d : ℝ → ℝ → M) {phi : ℝ → ℝ} {t x : ℝ}
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) :
    m62CurvatureVector F (fun y s => d (phi y) s) t x =
      m62CurvatureVector F d t (phi x) := by
  have hunit : spatialUnitTangent F (fun y s => d (phi y) s) t =
      fun y => spatialUnitTangent F d t (phi y) :=
    funext fun y => spatialUnitTangent_comp F d (hd (phi y))
      (hphi y).hasDerivAt (hpos y)
  unfold m62CurvatureVector
  rw [hunit]
  exact spatialDerivative_comp F d hS (hphi x).hasDerivAt (hpos x)

theorem curvatureJet_comp (F : RicciFlow n M (Set.Icc a b))
    (d : ℝ → ℝ → M) {phi : ℝ → ℝ} {t : ℝ}
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : ∀ x, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x))
    (hjet : ∀ i x, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, m63CurvatureJet F d i t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) (i : ℕ) (x : ℝ) :
    m63CurvatureJet F (fun y s => d (phi y) s) i t x =
      m63CurvatureJet F d i t (phi x) := by
  induction i generalizing x with
  | zero => exact curvatureVector_comp F d hd hphi hpos (hS x)
  | succ i ih =>
    change m62SpatialDerivative F (fun y s => d (phi y) s) t
      (fun y => m63CurvatureJet F (fun z s => d (phi z) s) i t y) x =
      m62SpatialDerivative F d t (fun y => m63CurvatureJet F d i t y) (phi x)
    rw [show (fun y => m63CurvatureJet F (fun z s => d (phi z) s) i t y) =
      (fun y => m63CurvatureJet F d i t (phi y)) from funext ih]
    exact spatialDerivative_comp F d (hjet i x) (hphi x).hasDerivAt (hpos x)

end PoincareConjecture.M63
