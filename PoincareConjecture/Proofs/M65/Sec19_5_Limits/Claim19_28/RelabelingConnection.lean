import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.SpeedRelabeling
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackAlgebra

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem m65CurveVelocity_comp {gamma : ℝ → M} {phi : ℝ → ℝ} {x d : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x))
    (hphi : HasDerivAt phi d x) :
    curveVelocity (n := n) (gamma ∘ phi) x =
      d • curveVelocity (n := n) gamma (phi x) := by
  have hchain := mfderiv_comp_apply (f := phi) (g := gamma) x
    hgamma hphi.differentiableAt.mdifferentiableAt (1 : ℝ)
  have hparam : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) phi x (1 : ℝ) = d := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hphi.deriv
  change curveVelocity (n := n) (gamma ∘ phi) x = _ at hchain
  erw [hparam] at hchain
  rw [hchain]
  let L : ℝ →L[ℝ] TangentSpace (𝓡 n) (gamma (phi x)) :=
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x)
  change L d = d • L 1
  simpa only [smul_eq_mul, mul_one] using L.map_smul d (1 : ℝ)

theorem m65Pullback_fixed_relabeling {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {gamma : ℝ → M}
    {Y : ∀ y, TangentSpace (𝓡 n) (gamma y)} {phi : ℝ → ℝ} {x d : ℝ}
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨gamma y, Y y⟩ : TangentBundle (𝓡 n) M)) (phi x))
    (hphi : HasDerivAt phi d x) :
    rampHorizontalCovariantDerivative D (gamma ∘ phi) (fun y => Y (phi y)) x =
      d • rampHorizontalCovariantDerivative D gamma Y (phi x) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) (gamma (phi x))
  let v : ℝ → EuclideanSpace ℝ (Fin n) := fun y => (e ⟨gamma y, Y y⟩).2
  rw [mdifferentiableAt_totalSpace] at hY
  have hv : DifferentiableAt ℝ v (phi x) := hY.2.differentiableAt
  have hdv : deriv (v ∘ phi) x = d • deriv v (phi x) :=
    (hv.hasDerivAt.scomp x hphi).deriv
  have hvelocity := m65CurveVelocity_comp hY.1 hphi
  change e.symmL ℝ (gamma (phi x)) (deriv (v ∘ phi) x) +
    D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y (phi x)))
      (gamma (phi x)) (curveVelocity (n := n) (gamma ∘ phi) x) =
    d • (e.symmL ℝ (gamma (phi x)) (deriv v (phi x)) +
      D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y (phi x)))
        (gamma (phi x)) (curveVelocity (n := n) gamma (phi x)))
  rw [hdv, hvelocity, map_smul, map_smul, smul_add]

end PoincareConjecture
