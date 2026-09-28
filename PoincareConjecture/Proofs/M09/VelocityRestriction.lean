import PoincareConjecture.Definitions.Ch06.LGeometry
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem curveVelocityWithin_eq_curveVelocity (γ : ℝ → M) (I : Set ℝ) (s : ℝ)
    (hI : UniqueDiffWithinAt ℝ I s)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s) :
    curveVelocityWithin (n := n) γ I s = curveVelocity (n := n) γ s :=
  congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 n) (γ s) ↦ L 1)
    (mfderivWithin_eq_mfderiv hI.uniqueMDiffWithinAt hγ)

def restrictVelocityExtension (γ : ℝ → M) (I K : Set ℝ) (hKI : K ⊆ I)
    (hI : UniqueDiffOn ℝ I) (hK : UniqueDiffOn ℝ K)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I)) :
    ParametricAlongCurveExtensionOn (n := n) K γ (curveVelocityWithin (n := n) γ K) where
  extension := E.extension
  domain := E.domain
  open_domain := E.open_domain
  graph_mem := fun s hs ↦ E.graph_mem s (hKI hs)
  smooth := E.smooth
  agrees := by
    intro s hs
    rw [E.agrees s (hKI hs),
      curveVelocityWithin_eq_curveVelocity γ I s (hI s (hKI hs)) (hγ s (hKI hs)),
      curveVelocityWithin_eq_curveVelocity γ K s (hK s hs) (hγ s (hKI hs))]

theorem restrictVelocityExtension_pullback {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (γ : ℝ → M) (I K : Set ℝ) (hKI : K ⊆ I)
    (hI : UniqueDiffOn ℝ I) (hK : UniqueDiffOn ℝ K)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (s : ℝ) (hs : s ∈ K) :
    pullbackCovariantDerivative F time γ (curveVelocityWithin (n := n) γ K) K
      (restrictVelocityExtension γ I K hKI hI hK hγ E) s =
      pullbackCovariantDerivative F time γ (curveVelocityWithin (n := n) γ I) I E s := by
  change deriv (fun r ↦ E.extension r (γ s)) s +
    (F.connection (time s)).connection (E.extension s) (γ s) (curveVelocityWithin γ K s) =
    deriv (fun r ↦ E.extension r (γ s)) s +
    (F.connection (time s)).connection (E.extension s) (γ s) (curveVelocityWithin γ I s)
  rw [curveVelocityWithin_eq_curveVelocity γ I s (hI s (hKI hs)) (hγ s (hKI hs)),
    curveVelocityWithin_eq_curveVelocity γ K s (hK s hs) (hγ s (hKI hs))]

theorem regularizedEquation_restrict {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (I K : Set ℝ) (hKI : K ⊆ I)
    (hI : UniqueDiffOn ℝ I) (hK : UniqueDiffOn ℝ K)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (s : ℝ) (hs : s ∈ K) (heq : regularizedLGeodesicEquation F T γ I E s) :
    regularizedLGeodesicEquation F T γ K
      (restrictVelocityExtension γ I K hKI hI hK hγ E) s := by
  intro W
  unfold regularizedEulerResidual
  rw [restrictVelocityExtension_pullback F (fun r ↦ T - r ^ 2) γ I K hKI hI hK hγ E s hs,
    curveVelocityWithin_eq_curveVelocity γ K s (hK s hs) (hγ s (hKI hs))]
  have h := heq W
  unfold regularizedEulerResidual at h
  rwa [curveVelocityWithin_eq_curveVelocity γ I s (hI s (hKI hs)) (hγ s (hKI hs))] at h

end PoincareConjecture.Proofs.M09
