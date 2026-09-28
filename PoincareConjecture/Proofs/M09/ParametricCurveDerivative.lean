import PoincareConjecture.Definitions.Ch06.LGeometry
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.Deriv.Comp








set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_parametric_curve (f : ℝ × M → W) (γ : ℝ → M) (s : ℝ)
    (hf : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, W)) f (s, γ s))
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s) :
    HasDerivAt (fun t ↦ f (t, γ t))
      (deriv (fun t ↦ f (t, γ s)) s +
        mvfderiv (𝓡 n) (fun x ↦ f (s, x)) (γ s) (curveVelocity γ s)) s := by
  have hgraph := (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) s).prodMk hγ.hasMFDerivAt
  have hcomp := (hf.hasMFDerivAt.comp s hgraph).hasFDerivAt.hasDerivAt
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) (I'' := 𝓘(ℝ, W))
    (v := (1, curveVelocity γ s)) hf
  have htime : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, W)) (fun t ↦ f (t, γ s)) s 1 =
      deriv (fun t ↦ f (t, γ s)) s := by
    exact (congrArg (fun L : ℝ →L[ℝ] W ↦ L 1)
      (mfderiv_eq_fderiv (f := fun t ↦ f (t, γ s)) (x := s))).trans
        fderiv_apply_one_eq_deriv
  have hvalue : mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, W)) f (s, γ s)
      (1, curveVelocity γ s) =
      deriv (fun t ↦ f (t, γ s)) s +
        mvfderiv (𝓡 n) (fun x ↦ f (s, x)) (γ s) (curveVelocity γ s) := by
    exact hsplit.trans (congrArg (· +
      mvfderiv (𝓡 n) (fun x ↦ f (s, x)) (γ s) (curveVelocity γ s)) htime)
  convert! hcomp using 1
  exact hvalue.symm

end PoincareConjecture.Proofs.M09
