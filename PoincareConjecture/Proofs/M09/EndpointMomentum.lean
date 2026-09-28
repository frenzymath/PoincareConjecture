import PoincareConjecture.Proofs.M09.SmoothSquareActionDifferential
import PoincareConjecture.Proofs.M09.SmoothBrokenCost
import PoincareConjecture.Proofs.M09.ExponentialPhaseLinearization
import PoincareConjecture.Proofs.M09.VelocityChainRules








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareChartMetric_tangent_pairing (F : RicciFlow n M J) (T s : ℝ)
    (q x : M) (hx : x ∈ (chartAt Q q).source)
    (v : TangentSpace (𝓡 n) x) (w : Q) :
    squareChartMetric F T q (s, (chartAt Q q) x)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt Q q) x v) w =
    (F.metric (T - s ^ 2)).inner x v
      (mfderiv (𝓡 n) (𝓡 n) (chartAt Q q).symm ((chartAt Q q) x) w) := by
  have hinv : (mfderiv (𝓡 n) (𝓡 n) (chartAt Q q).symm ((chartAt Q q) x))
      ((mfderiv (𝓡 n) (𝓡 n) (chartAt Q q) x) v) = v := by
    exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x ↦ L v)
      ((mdifferentiable_chart (I := 𝓡 n) q).symm_comp_deriv hx)
  change (F.metric (T - s ^ 2)).inner ((chartAt Q q).symm ((chartAt Q q) x))
    ((mfderiv (𝓡 n) (𝓡 n) (chartAt Q q).symm ((chartAt Q q) x))
      ((mfderiv (𝓡 n) (𝓡 n) (chartAt Q q) x) v))
    ((mfderiv (𝓡 n) (𝓡 n) (chartAt Q q).symm ((chartAt Q q) x)) w) = _
  rw [hinv, (chartAt Q q).left_inv hx]

noncomputable def lineMeetingMomentum (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (c r : ℝ) : Q →L[ℝ] ℝ :=
  squareChartMetric F T (A.squareFamily Z (Real.sqrt c))
    (Real.sqrt c, lineInteriorCoordinate A Z W c r)
    (initialLineChartPhase A Z W (A.squareFamily Z (Real.sqrt c)) (Real.sqrt c, r)).2

set_option backward.isDefEq.respectTransparency false in
theorem LineInteriorFamily.prefixAction_fderiv [ConnectedSpace M]
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {A : LExponentialFamily F T τmax p} {Z W : TangentSpace (𝓡 n) p} {c b : ℝ}
    (D : LineInteriorFamily A Z W c b) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (r : ℝ) (hr : (r, lineInteriorCoordinate A Z W c r) ∈ D.parameters) (w : ℝ × Q) :
    fderiv ℝ D.prefixAction (r, lineInteriorCoordinate A Z W c r) w =
      lineMeetingMomentum A Z W c r w.2 := by
  let q := A.squareFamily Z (Real.sqrt c)
  let e := chartAt Q q
  let a := lineInteriorCoordinate A Z W c
  have hsegment (s : ℝ) (hs : s ∈ Set.Icc 0 (Real.sqrt c)) : ((r, a r), s) ∈ D.domain :=
    D.segment_mem ⟨hr, hs.1, hs.2.trans (Real.sqrt_le_sqrt hcb.le)⟩
  have hcenter (s : ℝ) (hs : s ∈ Set.Icc 0 (Real.sqrt c)) :
      D.family ((r, a r), s) = A.squareFamily (Z + r • W) s :=
    D.recovery (r, a r) hr s ⟨hs.1, hs.2.trans (Real.sqrt_le_sqrt hcb.le)⟩
  have hfirst := fderiv_smoothSquareFamily_action hM04 hL hτmax hwindow
    A (Z + r • W) c hc (hcb.trans hmax) D.family D.domain D.domain_open D.smooth
    (r, a r) w hsegment hcenter
  have hleft : (fun u : ℝ ↦ D.family ((r, a r) + u • w, 0)) = fun _ : ℝ ↦ p := by
    funext u
    exact D.left _ _
  have hv0 : (curveVelocity (n := n) (fun u : ℝ ↦ D.family ((r, a r) + u • w, 0)) 0 : Q) = 0 := by
    rw [hleft]
    simp only [curveVelocity, mfderiv_const, ContinuousLinearMap.zero_apply]
  have hmark : (fun u : ℝ ↦ D.family ((r, a r) + u • w, Real.sqrt c)) =
      fun u : ℝ ↦ e.symm (a r + u • w.2) := by
    funext u
    exact D.marked _ _
  have htarget : a r ∈ e.target := D.target_mem (r, a r) hr
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have he : MDifferentiableAt (𝓡 n) (𝓡 n) e.symm (a r) :=
    (hchart.contMDiffAt (e.open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
  have hvm : (curveVelocity (n := n)
      (fun u : ℝ ↦ D.family ((r, a r) + u • w, Real.sqrt c)) 0 : Q) =
      mfderiv (𝓡 n) (𝓡 n) e.symm (a r) w.2 := by
    rw [hmark]
    exact curveVelocity_comp_initial_line e.symm (a r) w.2 he
  have hbase : e.symm (a r) = A.squareFamily (Z + r • W) (Real.sqrt c) :=
    (D.marked r (a r)).symm.trans (hcenter (Real.sqrt c) ⟨Real.sqrt_nonneg c, le_rfl⟩)
  have hsource : A.squareFamily (Z + r • W) (Real.sqrt c) ∈ e.source :=
    hbase ▸ e.map_target htarget
  have hpair := squareChartMetric_tangent_pairing F T (Real.sqrt c) q
    (A.squareFamily (Z + r • W) (Real.sqrt c)) hsource
    (curveVelocity (A.squareFamily (Z + r • W)) (Real.sqrt c)) w.2
  rw [Real.sq_sqrt hc.le] at hpair
  rw [hv0, hvm, map_zero, sub_zero] at hfirst
  exact hfirst.trans hpair.symm

end PoincareConjecture.Proofs.M09
