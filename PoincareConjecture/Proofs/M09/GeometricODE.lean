import PoincareConjecture.Proofs.M09.GeometricChartEquation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem regularizedCurve_chart_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (p : M) (γ : ℝ → M)
    (I : Set ℝ) (hI : IsOpen I)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ I)
    (hq : ∀ s ∈ I, γ s ∈ (chartAt V p).source)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (s : ℝ) (hs : s ∈ I) (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (heq : regularizedLGeodesicEquation F T γ I E s) :
    let a : ℝ → V := fun t ↦ (chartAt V p) (γ t)
    HasDerivAt (fun t ↦ (a t, deriv a t))
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (a s, deriv a s))) s := by
  let a : ℝ → V := fun t ↦ (chartAt V p) (γ t)
  have ha : ContDiffOn ℝ ∞ a I := (contMDiffOn_chart.comp hγ hq).contDiffOn
  have hv : ContDiffOn ℝ ∞ (deriv a) I := ha.deriv_of_isOpen hI (by simp)
  have had : ∀ t ∈ I, HasDerivAt a (deriv a t) t :=
    fun t ht ↦ ((ha.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hgd : ∀ t ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ t :=
    fun t ht ↦ (hγ.contMDiffAt (hI.mem_nhds ht)).mdifferentiableAt (by simp)
  have hvd : HasDerivAt (deriv a) (deriv (deriv a) s) s :=
    ((hv.contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hw := (regularizedEquation_iff_coordinate_acceleration F hM04 T b hb hwindow
    p γ (deriv a) I I hI (Set.Subset.refl I) hI.uniqueDiffOn hv hgd had hq E
    s hs htime _ hvd).mp heq
  exact (had s hs).prodMk (hvd.congr_deriv hw)

end PoincareConjecture.Proofs.M09
