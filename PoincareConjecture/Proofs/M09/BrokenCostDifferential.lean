import PoincareConjecture.Proofs.M09.EndpointMomentum
import PoincareConjecture.Proofs.M09.ShiftedCostDifferential

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
  {A : LExponentialFamily F T τmax p} {Z W : TangentSpace (𝓡 n) p} {c b : ℝ}

local notation "Q" => EuclideanSpace ℝ (Fin n)

namespace LineInteriorFamily

noncomputable def meetingCovector (D : LineInteriorFamily A Z W c b) (r : ℝ) : Q →L[ℝ] ℝ :=
  lineMeetingMomentum A Z W c r + fderiv ℝ D.tailAction (lineInteriorCoordinate A Z W c r)

theorem cost_first_derivatives [ConnectedSpace M]
    (D : LineInteriorFamily A Z W c b)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hc : 0 < c) (hcb : c < b) (hmax : b < τmax) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      fderiv ℝ D.cost (r, 0) (1, 0) = D.meetingCovector r (deriv (lineInteriorCoordinate A Z W c) r) ∧
      ∀ v : Q, fderiv ℝ D.cost (r, 0) (0, v) = D.meetingCovector r v := by
  let a := lineInteriorCoordinate A Z W c
  have ha : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ a r :=
    ((D.coordinate_smooth.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ h ↦ h.differentiableAt (by simp))
  have hfixed : ∀ᶠ r in 𝓝 (0 : ℝ), (0, a r) ∈ D.parameters :=
    (continuousAt_const.prodMk D.coordinate_smooth.continuousAt).preimage_mem_nhds
      (D.parameters_open.mem_nhds D.center_mem)
  filter_upwards [D.diagonal_mem, hfixed, ha] with r hr hrf hra
  have hprefix := (D.prefixAction_contDiffAt hM04 hτmax hwindow hc hcb hmax (r, a r) hr).differentiableAt
    (by simp)
  have htail := (D.tailAction_contDiffAt hM04 hτmax hwindow hc hcb hmax (a r) hrf).differentiableAt
    (by simp)
  have hform (w : ℝ × Q) : fderiv ℝ D.cost (r, 0) w =
      D.meetingCovector r (fderiv ℝ a r w.1 + w.2) :=
    shiftedCost_fderiv D.prefixAction D.tailAction a (lineMeetingMomentum A Z W c r) r
      hprefix htail hra (D.prefixAction_fderiv hM04 hL hτmax hwindow hc hcb hmax r hr) w
  refine ⟨?_, ?_⟩
  · simpa only [add_zero, fderiv_apply_one_eq_deriv, a] using hform (1, 0)
  · intro v
    simpa only [map_zero, zero_add] using hform (0, v)

end LineInteriorFamily

end PoincareConjecture.Proofs.M09
