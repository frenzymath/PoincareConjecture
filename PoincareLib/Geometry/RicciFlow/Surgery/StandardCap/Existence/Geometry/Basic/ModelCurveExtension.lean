import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.ModelTangentSection
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.PullbackExtension
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.PullbackExtension
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.VelocityRestriction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.VelocityRestriction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Constant-spatial velocity extensions in the model space

The parameter velocity is extended constantly in the spatial variable.
Actual within derivatives agree at every point of a uniquely differentiable
parameter set, including its endpoints. M09 extension independence then
retains the ordinary square-root Euler equation.
Source: Morgan-Tian Proposition 12.13, pp. 304-306; the endpoint argument
in `proof-work/tasks/M34/derivations/ordinary-square-survival.md`.
-/

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M34

variable {n : ℕ}

/-- The actual model-space curve velocity equals its ordinary derivative,
including the common totalized value (Proposition 12.13). -/
theorem model_curveVelocity_eq_deriv (alpha : ℝ → EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    curveVelocity (n := n) alpha s = deriv alpha s := by
  simp only [curveVelocity, mfderiv_eq_fderiv, deriv]
  rfl

/-- A smooth model-space curve has a smooth velocity on its open domain
(Proposition 12.13, pp. 304-306). -/
theorem model_curveVelocity_contDiffOn {alpha : ℝ → EuclideanSpace ℝ (Fin n)}
    {O : Set ℝ} (hO : IsOpen O) (ha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha O) :
    ContDiffOn ℝ ∞ (curveVelocity (n := n) alpha) O := by
  have hv : curveVelocity (n := n) alpha = deriv alpha :=
    funext (model_curveVelocity_eq_deriv alpha)
  rw [hv]
  exact ha.contDiffOn.deriv_of_isOpen hO (m := ∞) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The actual parameter velocity, constant in space, is a valid smooth
extension along the entire closed parameter set (Proposition 12.13). -/
noncomputable def modelCurveVelocityExtension
    (alpha : ℝ → EuclideanSpace ℝ (Fin n)) (K O : Set ℝ)
    (hO : IsOpen O) (hKO : K ⊆ O) (hK : UniqueDiffOn ℝ K)
    (ha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha O) :
    ParametricAlongCurveExtensionOn (n := n) K alpha
      (curveVelocityWithin (n := n) alpha K) where
  extension := fun r _ => curveVelocity (n := n) alpha r
  domain := O ×ˢ univ
  open_domain := hO.prod isOpen_univ
  graph_mem := fun s hs => ⟨hKO hs, mem_univ _⟩
  smooth := by
    have hv := (model_curveVelocity_contDiffOn hO ha).contMDiffOn
    exact (contMDiff_modelTangentMk (𝓡 n) ∞).comp_contMDiffOn
      (contMDiffOn_snd.prodMk (hv.comp contMDiffOn_fst (fun _ hs => hs.1)))
  agrees := by
    intro s hs
    exact (PoincareMT.Proofs.M09.curveVelocityWithin_eq_curveVelocity alpha K s
      (hK s hs) ((ha.contMDiffAt (hO.mem_nhds (hKO hs))).mdifferentiableAt (by simp))).symm

/-- Replacing a supplied extension by the constant-spatial velocity
extension leaves the actual covariant derivative unchanged, including
parameter endpoints (Proposition 12.13, pp. 304-306). -/
theorem modelCurveVelocityExtension_covariantDerivative
    {J : Set ℝ} (F : RicciFlow n (EuclideanSpace ℝ (Fin n)) J)
    (time : ℝ → ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin n)) (K O : Set ℝ)
    (hO : IsOpen O) (hKO : K ⊆ O) (hK : UniqueDiffOn ℝ K)
    (ha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha O)
    (B : ParametricAlongCurveExtensionOn (n := n) K alpha
      (curveVelocityWithin (n := n) alpha K))
    {s : ℝ} (hs : s ∈ K) :
    pullbackCovariantDerivative F time alpha (curveVelocityWithin alpha K) K B s =
      pullbackCovariantDerivative F time alpha (curveVelocityWithin alpha K) K
        (modelCurveVelocityExtension alpha K O hO hKO hK ha) s :=
  PoincareMT.Proofs.M09.pullbackCovariantDerivative_extension_independent
    F time alpha _ K B _ s hs (hK s hs)
      ((ha.contMDiffAt (hO.mem_nhds (hKO hs))).mdifferentiableAt (by simp))

end PoincareMT.M34
