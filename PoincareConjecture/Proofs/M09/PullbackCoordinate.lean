import PoincareConjecture.Proofs.M09.ChartFieldDerivative
import PoincareConjecture.Proofs.M09.SquareChartConnection
import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M09.VelocityRestriction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem pullbackCovariantDerivative_eq_chart {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (γ : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (γ s))
    (K U : Set ℝ) (E : ParametricAlongCurveExtensionOn K γ Y)
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hq : ∀ s ∈ U, γ s ∈ (chartAt V p).source)
    (v : ℝ → V) (hv : ContDiffOn ℝ ∞ v U)
    (heq : ∀ s ∈ K ∩ U, chartVectorField p (v s) (γ s) = Y s)
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) (hKd : UniqueDiffWithinAt ℝ K s)
    (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Y K E s =
      chartVectorField p
        (deriv v s + coordinateConnection (squareChartMetric F T p)
          (s, (chartAt V p) (γ s)) (deriv (fun r ↦ (chartAt V p) (γ r)) s) (v s))
        (γ s) := by
  let a : ℝ → V := fun r ↦ (chartAt V p) (γ r)
  have ha : ContDiffOn ℝ ∞ a U :=
    (contMDiffOn_chart.comp hγ hq).contDiffOn
  have had : HasDerivAt a (deriv a s) s :=
    ((ha.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp)).hasDerivAt
  have hvd : HasDerivAt v (deriv v s) s :=
    ((hv.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp)).hasDerivAt
  have hgd := (hγ.contMDiffAt (hU.mem_nhds hsU)).mdifferentiableAt (by simp)
  have hvel : curveVelocityWithin (n := n) γ K s = chartVectorField p (deriv a s) (γ s) :=
    (curveVelocityWithin_eq_curveVelocity γ K s hKd hgd).trans
      (chartVectorField_coordinate_velocity p γ s (deriv a s) (hq s hsU) hgd had).symm
  have hpull := pullbackCovariantDerivative_chart_field_local F (fun r ↦ T - r ^ 2)
    p γ Y K U E s hs hU hsU hKd hgd v hv (fun r hr ↦ hq r hr.2) heq (deriv v s) hvd
  have hconn := squareChartConnection_eq F T b hb hwindow p s htime
    (a s) ((chartAt V p).map_source (hq s hsU)) (deriv a s) (v s)
  dsimp only [a] at hconn
  rw [(chartAt V p).left_inv (hq s hsU)] at hconn
  rw [hvel, ← hconn] at hpull
  exact hpull.trans ((mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s)).inverse.map_add _ _).symm

end PoincareConjecture.Proofs.M09
