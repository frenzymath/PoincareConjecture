import PoincareConjecture.Proofs.M10.GeometricBranchODE
import PoincareConjecture.Proofs.M10.LocalODE
import PoincareConjecture.Proofs.M10.TerminalVelocity
import PoincareConjecture.Proofs.M10.EulerTail









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem noncritical_gamma_eventuallyEq_of_terminal_velocity
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hZ : Function.Bijective (G.toLExponentialFamily.sliceDifferential Z τ))
    (hW : Function.Bijective (G.toLExponentialFamily.sliceDifferential W τ))
    (hend : G.gamma Z τ = G.gamma W τ)
    (hvel : hend ▸ curveVelocity (n := n) (G.gamma Z) τ =
      curveVelocity (n := n) (G.gamma W) τ) :
    G.gamma Z =ᶠ[𝓝 τ] G.gamma W := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let q := G.gamma Z τ
  let E := endpointCoordinates G q
  let B := coordinateBackwardMetric F T q
  let R := coordinateScalarCurvature F T q
  have hz : (Z, τ) ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hw : (W, τ) ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hqZ : G.gamma Z τ ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source :=
    mem_chart_source _ _
  have hqW : G.gamma W τ ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source := hend ▸ hqZ
  have hEeq : E (Z, τ) = E (W, τ) := congrArg (extChartAt (𝓡 n) q) hend
  have hframe : ∀ (x y : M) (hxy : x = y)
      (u : TangentSpace (𝓡 n) x) (v : TangentSpace (𝓡 n) y), hxy ▸ u = v →
      (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) q).continuousLinearMapAt ℝ x u =
      (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) q).continuousLinearMapAt ℝ y v := by
    intro x y hxy u v huv
    subst y
    exact congrArg _ huv
  have hVeq : fderiv ℝ E (Z, τ) (0, 1) = fderiv ℝ E (W, τ) (0, 1) := by
    rw [endpointCoordinates_time G q (Z, τ) hz hqZ,
      endpointCoordinates_time G q (W, τ) hw hqW]
    exact hframe _ _ hend _ _ hvel
  have hstate : actionBranchPhase E B Z τ = actionBranchPhase E B W τ := by
    change (τ, E (Z, τ), actionBranchMomentum E B (Z, τ)) =
      (τ, E (W, τ), actionBranchMomentum E B (W, τ))
    refine Prod.ext (show τ = τ from rfl) (Prod.ext hEeq ?_)
    dsimp only [actionBranchMomentum]
    rw [hEeq, hVeq]
  have hB : ContDiffAt ℝ ∞ B (E (Z, τ), τ) :=
    coordinateBackwardMetric_contDiffAt hwindow q hτ hmax
  have hR : ContDiffAt ℝ ∞ R (E (Z, τ), τ) :=
    coordinateScalarCurvature_contDiffAt_of_noncritical hwindow G (Z, τ) hz hZ
  have hi : (B (E (Z, τ), τ)).IsInvertible :=
    coordinateBackwardMetric_isInvertible q _
      ((extChartAt (𝓡 n) q).map_source (mem_extChartAt_source q))
  have hfield : ContDiffAt ℝ 1 (phaseField B R) (actionBranchPhase E B Z τ) :=
    phaseField_contDiffAt hB hR hτ hi
  have hsolZ := noncritical_branch_solves hwindow G q (Z, τ) hz rfl hZ
  have hsolW := noncritical_branch_solves hwindow G q (W, τ) hw hend.symm hW
  have hphase := eventuallyEq_of_contDiffAt_vectorField hfield hsolZ hsolW hstate
  have hcontZ : ContinuousAt (G.gamma Z) τ :=
    ((G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).comp τ
      (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
  have hcontW : ContinuousAt (G.gamma W) τ :=
    ((G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hw)).comp τ
      (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
  filter_upwards [hphase,
    hcontZ ((chartAt (EuclideanSpace ℝ (Fin n)) q).open_source.mem_nhds hqZ),
    hcontW ((chartAt (EuclideanSpace ℝ (Fin n)) q).open_source.mem_nhds hqW)]
    with t ht htZ htW
  have htZ' : G.gamma Z t ∈ (extChartAt (𝓡 n) q).source := by
    simpa only [Set.mem_preimage, extChartAt_source] using htZ
  have htW' : G.gamma W t ∈ (extChartAt (𝓡 n) q).source := by
    simpa only [Set.mem_preimage, extChartAt_source] using htW
  apply (extChartAt (𝓡 n) q).injOn htZ' htW'
  exact congrArg (fun a : ℝ × EuclideanSpace ℝ (Fin n) ×
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ↦ a.2.1) ht

variable [ConnectedSpace M]


theorem minimizing_noncritical_gamma_eqOn
    (hL : LGeodesicTheory F T τmax) (hwindow : Icc (T - τmax) T ⊆ J)
    (G : LExponentialGeometry F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hZ : IsMinimizingBackwardLPath F T 0 τ (G.path Z τ hτ hmax))
    (hW : IsMinimizingBackwardLPath F T 0 τ (G.path W τ hτ hmax))
    (hend : G.gamma Z τ = G.gamma W τ)
    (hl : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ reducedLength F T p q τ)
      (G.gamma Z τ))
    (hcZ : Function.Bijective (G.toLExponentialFamily.sliceDifferential Z τ))
    (hcW : Function.Bijective (G.toLExponentialFamily.sliceDifferential W τ)) :
    EqOn (G.gamma Z) (G.gamma W) (Icc 0 τ) := by
  have hvel := minimizing_terminal_velocity_eq hL G Z W hτ hmax hZ hW hend hl hcZ.2 hcW.2
  have hlocal := noncritical_gamma_eventuallyEq_of_terminal_velocity
    hwindow G Z W hτ hmax hcZ hcW hend hvel
  have heq := eulerPaths_eqOn_of_eventuallyEq hL hmax.le
    (hL.euler_lagrange 0 τ le_rfl hτ hmax.le (G.path Z τ hτ hmax) hZ)
    (hL.euler_lagrange 0 τ le_rfl hτ hmax.le (G.path W τ hτ hmax) hW)
    (by simpa only [G.path_eq] using hlocal)
  simpa only [G.path_eq] using heq

end PoincareConjecture.M10
