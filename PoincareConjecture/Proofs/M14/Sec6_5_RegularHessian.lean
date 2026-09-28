import PoincareConjecture.Proofs.M14.Sec6_5_HessianIndexComparison
import PoincareConjecture.Proofs.M14.Sec6_5_RegularSpatialDerivative











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}



theorem jointImage_finiteValueDomain (E : M14ExponentialFamily G T x) {q : G.Point}
    (hq : q ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) :
    M14FiniteValueDomain G T 0 (T - G.spacetime.timeFunction q) x q := by
  obtain ⟨⟨⟨Z, s⟩, hz⟩, rfl⟩ := hq
  obtain ⟨_, _, p, hp, _, _⟩ := jointDomain_action_branch E hz
  rw [E.clock Z s (jointDomain_subset_domain E hz), sub_sub_cancel]
  exact finiteValueDomain_of_minimizing p hp

private theorem horizontal_momentum_transport {q r : G.Point} (h : q = r)
    (f : G.Point → ℝ) (A : G.Horizontal q) (c : ℝ)
    (hd : ∀ W : G.Horizontal r,
      mvfderiv (spacetimeModel n) f r W.val =
        G.spacetime.horizontalMetric.inner r (h ▸ A) W / c) :
    ∀ W : G.Horizontal q, mvfderiv (spacetimeModel n) f q W.val =
      G.spacetime.horizontalMetric.inner q A W / c := by
  cases h
  exact hd

private theorem hessian_pair_parameter_congr (γ : ℝ → G.Point)
    (Y : ∀ r, G.Horizontal (γ r)) (f : G.Point → ℝ) {r s T τ : ℝ} (h : r = s)
    (hr : G.spacetime.timeFunction (γ r) = T - τ)
    (hs : G.spacetime.timeFunction (γ s) = T - τ) :
    M14ReducedLengthHessianPairing G ⟨γ r, hr⟩ f (Y r) (Y r) =
      M14ReducedLengthHessianPairing G ⟨γ s, hs⟩ f (Y s) (Y s) := by
  subst s
  rfl




theorem reducedLengthHessian_joint_le_index
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2)
    {Y : ∀ r, G.Horizontal ((E.square_path Z s hs hpos).curve r)}
    (EY : M14PullbackExtension G (E.square_path Z s hs hpos).curve
      (M14SqrtParameterInterval 0 (s ^ 2)) Y) (hleft : Y 0 = 0) :
    M14ReducedLengthHessianPairing G ⟨(E.square_path Z s hs hpos).curve s, hq⟩
        (M14ReducedLengthAt G T 0 x) (Y s) (Y s) ≤
      (∫ r in 0..s, pullbackIndexPairDensity (E.square_path Z s hs hpos) EY EY r) / (2 * s) := by
  let R := E.square_path Z s hs hpos
  let p := E.path Z s hs hpos
  let O := range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)
  have hO : IsOpen O := jointMap_range_isOpen E
  have hpoint' : R.curve (Real.sqrt (s ^ 2)) = E.gamma Z s := by
    rw [Real.sqrt_sq hpos.le]
    exact hpoint
  have hp : R.curve (Real.sqrt (s ^ 2)) ∈ O := hpoint'.symm ▸ ⟨⟨(Z, s), hz⟩, rfl⟩
  obtain ⟨H, hZH⟩ := jointDomain_stableSet E hz
  have hmin : M14IsMinimizing p := exponentialPath_minimizing_of_uniqueBranch E hpos hs
    (stableInitialVector_unique_branch E ((H.carrier_exact Z).mp hZH))
  have hvalue : M14ReducedLengthAt G T 0 x (R.curve (Real.sqrt (s ^ 2))) =
      M14BackwardLAction G p / (2 * Real.sqrt (s ^ 2)) := by
    rw [hpoint', reducedLengthAt_jointEndpoint E hz, Real.sqrt_sq hpos.le,
      E.action_eq Z s hs hpos]
  have hfinite : ∀ᶠ q in 𝓝 (R.curve (Real.sqrt (s ^ 2))),
      M14FiniteValueDomain G T 0 (T - G.spacetime.timeFunction q) x q :=
    Filter.eventually_of_mem (hO.mem_nhds hp) (fun _ hq => jointImage_finiteValueDomain E hq)
  have hd : ∀ W : G.Horizontal (R.curve s),
      mvfderiv (spacetimeModel n) (M14ReducedLengthAt G T 0 x) (R.curve s) W.val =
        G.spacetime.horizontalMetric.inner (R.curve s) (R.horizontal_velocity s) W / (2 * s) :=
    horizontal_momentum_transport hpoint (M14ReducedLengthAt G T 0 x) (R.horizontal_velocity s)
      (2 * s) (reducedLengthAt_horizontal_differential hCoordinates hM04 hM12 E hs hpos hz hpoint)
  have hclock : G.spacetime.timeFunction (R.curve (Real.sqrt (s ^ 2))) = T - s ^ 2 := by
    rw [Real.sqrt_sq hpos.le]
    exact hq
  have h := hessian_le_pullback_index hCoordinates hM04 hM12 hmin
    (M14ReducedLengthAt G T 0 x) O hO hp (reducedLengthAt_contMDiffOn_jointImage hM04 hM12 E)
    hvalue (Eventually.of_forall (fun _ => le_rfl)) hfinite
    (by rw [Real.sqrt_sq hpos.le]; exact hd) hclock EY
    (by rw [Real.sqrt_zero]; exact hleft)
  rw [hessian_pair_parameter_congr R.curve Y (M14ReducedLengthAt G T 0 x)
    (Real.sqrt_sq hpos.le) hclock hq, Real.sqrt_zero, Real.sqrt_sq hpos.le] at h
  exact h

end PoincareConjecture.M14
