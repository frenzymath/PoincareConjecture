import PoincareConjecture.Proofs.M62.Sec19_1_PullbackAlgebra
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64Pullback_covariantDerivative_eq_affine_parameter
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : E → M} {Y : (q : E) → TangentSpace (𝓡 n) (f q)}
    {h : ℝ → E} {x : ℝ} (hh : DifferentiableAt ℝ h x)
    (hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f (h x))
    (hY : MDifferentiableAt 𝓘(ℝ, E) ((𝓡 n).prod (𝓡 n))
      (fun q => (⟨f q, Y q⟩ : TangentBundle (𝓡 n) M)) (h x)) :
    let H := fun y : ℝ => h x + (y - x) • deriv h x
    rampHorizontalCovariantDerivative D (fun y => f (h y)) (fun y => Y (h y)) x =
      rampHorizontalCovariantDerivative D (fun y => f (H y)) (fun y => Y (H y)) x := by
  let H := fun y : ℝ => h x + (y - x) • deriv h x
  have hHx : H x = h x := by simp [H]
  have hH : HasDerivAt H (deriv h x) x := by
    simpa only [H, id_eq, one_smul] using!
      (((hasDerivAt_id x).sub_const x).smul_const (deriv h x)).const_add (h x)
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (f (h x))
  let y : E → EuclideanSpace ℝ (Fin n) := fun q => (e ⟨f q, Y q⟩).2
  have hy : DifferentiableAt ℝ y (h x) := by
    rw [mdifferentiableAt_totalSpace] at hY
    exact hY.2.differentiableAt
  have hdy : deriv (fun z => y (h z)) x = deriv (fun z => y (H z)) x := by
    have ha := hy.hasFDerivAt.comp_hasDerivAt x hh.hasDerivAt
    have hb := (hHx.symm ▸ hy).hasFDerivAt.comp_hasDerivAt x hH
    change deriv (y ∘ h) x = deriv (y ∘ H) x
    rw [ha.deriv, hb.deriv, hHx]
  have hvh : curveVelocity (n := n) (fun z => f (h z)) x =
      mfderiv 𝓘(ℝ, E) (𝓡 n) f (h x) (deriv h x) := by
    have hc := mfderiv_comp_apply x hf hh.mdifferentiableAt (1 : ℝ)
    simpa +instances only [Function.comp_def, curveVelocity, mfderiv_eq_fderiv, deriv]
      using! hc
  have hvH : curveVelocity (n := n) (fun z => f (H z)) x =
      mfderiv 𝓘(ℝ, E) (𝓡 n) f (h x) (deriv h x) := by
    have hc := mfderiv_comp_apply x (hHx.symm ▸ hf) hH.differentiableAt.mdifferentiableAt
      (1 : ℝ)
    have hc' : curveVelocity (n := n) (fun z => f (H z)) x =
        mfderiv 𝓘(ℝ, E) (𝓡 n) f (H x) (deriv H x) := by
      simpa +instances only [Function.comp_def, curveVelocity, mfderiv_eq_fderiv, deriv]
        using! hc
    have hp : (H x, deriv H x) = (h x, deriv h x) := Prod.ext hHx hH.deriv
    exact hc'.trans (congrArg (fun q : E × E =>
      (mfderiv 𝓘(ℝ, E) (𝓡 n) f q.1 q.2 : EuclideanSpace ℝ (Fin n))) hp)
  have hright : rampHorizontalCovariantDerivative D (fun z => f (H z))
      (fun z => Y (H z)) x =
      e.symmL ℝ (f (h x)) (deriv (fun z => y (H z)) x) +
        D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y (h x)))
          (f (h x)) (curveVelocity (fun z => f (H z)) x) := by
    let C : E → EuclideanSpace ℝ (Fin n) := fun q =>
      let eq := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (f q)
      eq.symmL ℝ (f q) (deriv (fun z => (eq ⟨f (H z), Y (H z)⟩).2) x) +
        D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y q))
          (f q) (curveVelocity (fun z => f (H z)) x)
    exact congrArg C hHx
  change rampHorizontalCovariantDerivative D (fun z => f (h z)) (fun z => Y (h z)) x = _
  rw [hright]
  change e.symmL ℝ (f (h x)) (deriv (fun z => y (h z)) x) +
      D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y (h x)))
        (f (h x)) (curveVelocity (fun z => f (h z)) x) = _
  rw [hdy, hvh, hvH]

end PoincareConjecture
