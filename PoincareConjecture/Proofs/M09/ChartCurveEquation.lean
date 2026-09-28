import PoincareConjecture.Proofs.M09.ChartCurveExtension
import PoincareConjecture.Proofs.M09.SquareChartPairing








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem chartCurve_regularized_equation {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (a v : ℝ → E) (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U)
    (hI : UniqueDiffOn ℝ I) (hv : ContDiffOn ℝ ∞ v U)
    (ha : ∀ s ∈ I, HasDerivAt a (v s) s)
    (hy : ∀ s ∈ I, a s ∈ (chartAt E p).target)
    (htime : I ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hdv : ∀ s ∈ I, HasDerivAt v
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (a s, v s))).2 s) :
    ∀ s ∈ I, regularizedLGeodesicEquation F T (fun r ↦ (chartAt E p).symm (a r)) I
      (chartCurveVelocityExtension p a v U I hU hIU hI hv ha hy) s := by
  intro s hs W
  obtain ⟨w, rfl⟩ := (inverseChartDifferential_bijective p (a s) (hy s hs)).2 W
  unfold regularizedEulerResidual
  rw [chartCurveVelocityExtension_pullback F (fun r ↦ T - r ^ 2) p a v U I
    hU hIU hI hv ha hy s hs _ (hdv s hs),
    curveVelocityWithin_inverseChart p a I s (v s) (hI s hs) (ha s hs) (hy s hs)]
  exact regularizedCoordinatePhase_geometric_pairing F hM04 T b hb hwindow p s
    (htime hs) (a s) (v s) w (hy s hs)

end PoincareConjecture.Proofs.M09
