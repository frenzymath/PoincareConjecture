import PoincareConjecture.Proofs.M09.ExponentialAction
import PoincareConjecture.Proofs.M09.ExponentialActionDifferential
import PoincareConjecture.Proofs.M09.ExponentialActionTime
import PoincareConjecture.Proofs.M09.InitialVectorJacobi
import PoincareConjecture.Proofs.M09.MinimizerLifts
import PoincareConjecture.Proofs.M09.BoundedMinimizingVectors
import PoincareConjecture.Proofs.M09.RegularChart
import PoincareConjecture.Proofs.M09.RegularDomainOpen
import PoincareConjecture.Proofs.M09.RegularPointConstruction
import PoincareConjecture.Proofs.M09.BackwardNesting
import PoincareConjecture.Proofs.M09.BoundedInitialCoverage








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
  [SecondCountableTopology M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_exists_geometry {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p) :
    Nonempty (LExponentialGeometry F T τmax p) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  obtain ⟨G, hsource, hforward, hforward_smooth, hinverse_smooth, htarget, htime⟩ :=
    lExponentialFamily_exists_regular_chart F hM04 T τmax hτmax hwindow hcurvature hL p A
  let regularPoint : ∀ z : M × ℝ, z ∈ G.target →
      ReducedLengthRegularPoint F T τmax p z.1 z.2 :=
    fun z hz => Classical.choose (lExponentialFamily_exists_regularPoint_of_chart
      hM04 hτmax hwindow hL A G hsource hforward hinverse_smooth htarget htime z hz)
  have regularPoint_spec : ∀ (z : M × ℝ) (hz : z ∈ G.target),
      (regularPoint z hz).path.curve = A.gamma (G.symm z).1 ∧
      (regularPoint z hz).neighborhood = G.target ∧
      (regularPoint z hz).representative =
        (fun w ↦ A.action (G.symm w).1 w.2 / (2 * Real.sqrt w.2)) := by
    intro z hz
    exact Classical.choose_spec (lExponentialFamily_exists_regularPoint_of_chart
      hM04 hτmax hwindow hL A G hsource hforward hinverse_smooth htarget htime z hz)
  refine ⟨{
    toLExponentialFamily := A
    action_smooth := lExponentialFamily_action_contDiffOn hM04 hτmax hwindow A
    action_initial_differential := ?_
    action_time_derivative := ?_
    jacobi_differential := ?_
    minimizers_lift := ?_
    minimizing_initial_bounded := ?_
    regular_chart := G
    regular_source := hsource
    regular_forward := hforward
    regular_forward_smooth := hforward_smooth
    regular_inverse_smooth := hinverse_smooth
    regular_target_times := htarget
    regular_inverse_time := htime
    regular_domain_eq_local := lExponentialFamily_regularDomain_eq_local F hM04 T τmax
      hτmax hwindow hcurvature hL p A
    regular_point := regularPoint
    regular_point_path := ?_
    regular_point_neighborhood := ?_
    regular_point_representative := ?_
    backward_nesting := ?_
    bounded_initial_coverage := ?_ }⟩
  · intro Z τ hτ hmax W
    exact lExponentialFamily_action_initial_differential hM04 hL hτmax hwindow A Z τ hτ hmax W
  · intro Z τ hτ hmax
    exact lExponentialFamily_action_hasDerivAt hM04 hwindow A Z τ hτ hmax
  · intro Z W b hb hmax
    exact lExponentialFamily_jacobi_differential hM04 hτmax hwindow A Z W b hb hmax
  · intro τ hτ hmax q hq0 hmin
    exact lExponentialFamily_minimizers_lift hM04 hL hτmax hwindow A τ hτ hmax q hq0 hmin
  · intro Q hQ hQt
    obtain ⟨R, hR, hbound⟩ := lExponentialFamily_minimizing_initial_bounded F hM04 T τmax
      hτmax hwindow hcurvature hL p A Q hQ hQt
    refine ⟨R, hR, ?_⟩
    intro Z τ hτ hmax hQmem hmin
    exact hbound Z τ hτ hmax hQmem hmin
  · intro z hz
    intro s hs
    rw [(regularPoint_spec z hz).1]
  · intro z hz
    rw [(regularPoint_spec z hz).2.1]
  · intro z hz
    exact (regularPoint_spec z hz).2.2
  · intro Z τ₂ hτ₂ τ₁ hτ₁ hle
    exact lExponentialFamily_backward_nesting hM04 hL hτmax hwindow A Z τ₂ hτ₂ τ₁ hτ₁ hle
  · intro a ha
    exact lExponentialFamily_bounded_initial_coverage F hM04 T τmax hτmax hwindow hcurvature hL p A a ha

end PoincareConjecture.Proofs.M09
