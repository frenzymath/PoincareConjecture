import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCurveCoefficients
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessAmbientAcceleration










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι





theorem parabolic_gauge_of_ambient_equation (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (q : ℝ → ℝ → M) {t x : ℝ}
    (hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t))
    (htime : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => q x s) t)
    (hpde : deriv (fun s => e (q x s)) t =
      ambientCurvePrincipal F ρ t (e (q x t)) (deriv (fun y => e (q y t)) x) •
          deriv (deriv (fun y => e (q y t))) x +
        ambientCurveLower F e ρ t (e (q x t)) (deriv (fun y => e (q y t)) x)) :
    curveVelocity (fun s => q x s) t =
      (curveSpeed F q t x ^ 2)⁻¹ •
        rampHorizontalCovariantDerivative (F.connection t) (fun y => q y t)
          (fun y => curveVelocity (fun z => q z t) y) x := by
  let p := q x t
  let D : TangentSpace (𝓡 n) p →L[ℝ] W := mfderiv (𝓡 n) 𝓘(ℝ, W) e p
  let X := curveVelocity (n := n) (fun y => q y t) x
  let V := curveVelocity (n := n) (fun s => q x s) t
  let Y := rampHorizontalCovariantDerivative (F.connection t) (fun y => q y t)
    (fun y => curveVelocity (fun z => q z t) y) x
  let H := coordinateHessian (F.connection t) e p X X
  let A := (curveSpeed F q t x ^ 2)⁻¹
  obtain ⟨_hr, _hDr, hleft⟩ := smooth_retraction_differentials he hU heU hρ hρe
  have hpushspace : deriv (fun y => e (q y t)) x =
      D X := by
    have hc : fderiv ℝ (fun y => e (q y t)) x =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e p).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hspace x).mdifferentiableAt (by norm_num))
    exact congrArg (fun D : ℝ →L[ℝ] W => D 1) hc
  have hpushtime : deriv (fun s => e (q x s)) t =
      D V := by
    have hc : fderiv ℝ (fun s => e (q x s)) t =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e p).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => q x s) t) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp t (he.mdifferentiable (by simp)).mdifferentiableAt htime
    exact congrArg (fun D : ℝ →L[ℝ] W => D 1) hc
  have hA : ambientCurvePrincipal F ρ t (e (q x t))
      (deriv (fun y => e (q y t)) x) = A := by
    rw [hpushspace]
    unfold ambientCurvePrincipal
    change ((F.metric t).inner (ρ (e p))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e p) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p X))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e p) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p X)))⁻¹ = A
    erw [hleft p X, hρe p]
    exact congrArg (fun z : ℝ => z⁻¹) (M62.speed_sq F q t x).symm
  have hB : ambientCurveLower F e ρ t (e (q x t))
      (deriv (fun y => e (q y t)) x) = -(A • H) := by
    unfold ambientCurveLower
    rw [hA, hpushspace]
    change -(A • coordinateHessian (F.connection t) e (ρ (e p))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e p) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p X))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e p) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p X))) = _
    erw [hleft p X, hρe p]
  have hacc : deriv (deriv (fun y => e (q y t))) x =
      H + D Y :=
    secondDeriv_embedding_eq_hessian_add_acceleration (F.connection t) he hspace x
  have hpush : D V = A • D Y := by
    rw [hpushtime, hA, hB, hacc, smul_add] at hpde
    calc
      _ = A • H + A • D Y + -(A • H) := hpde
      _ = _ := by abel
  have hpull := congrArg (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e p)) hpush
  dsimp only [D] at hpull
  erw [map_smul, hleft p V, hleft p Y] at hpull
  exact hpull

end PoincareConjecture.M63
