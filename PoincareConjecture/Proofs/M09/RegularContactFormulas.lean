import PoincareConjecture.Proofs.M09.SpacetimeContact
import PoincareConjecture.Proofs.M09.MinimizerLifts
import PoincareConjecture.Proofs.M09.HarnackIntegral
import PoincareConjecture.Proofs.M09.HarnackCongruence

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T2Space M]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem regular_first_formulas {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p q : M} {b : ℝ}
    (A : LExponentialFamily F T τmax p) (r : ReducedLengthRegularPoint F T τmax p q b) :
    deriv (fun s ↦ r.representative (q, s)) b =
        (F.connection (T - b)).scalarCurvature q - r.representative (q, b) / b +
          reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative b /
            (2 * b * Real.sqrt b) ∧
      reducedLengthGradientNormSq F T r.representative b q =
        r.representative (q, b) / b -
          reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative b /
            (b * Real.sqrt b) - (F.connection (T - b)).scalarCurvature q := by
  obtain ⟨Z, hpath, _⟩ := lExponentialFamily_minimizers_lift hM04 hL hτmax hwindow
    A b r.tau_pos r.tau_lt r.path r.path_start r.minimizing
  have hend : A.gamma Z b = q := (hpath ⟨r.tau_pos.le, le_rfl⟩).symm.trans r.path_end
  have hvalue := regular_representative_eq_family_action r A Z hpath
  have hB : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      r.representative (A.gamma Z b, b) := by
    rw [hend]
    exact r.representative_spacetime_smooth
  have hvalue' : r.representative (A.gamma Z b, b) = A.action Z b / (2 * Real.sqrt b) := by
    rw [hend]
    exact hvalue
  have hlow : ∀ᶠ w in 𝓝 (A.gamma Z b, b),
      r.representative w ≤ reducedLength F T p w.1 w.2 := by
    rw [hend]
    filter_upwards [r.neighborhood_open.mem_nhds r.center_mem] with w hw
    exact (r.representative_eq w hw).le
  obtain ⟨_, hgrad, htime⟩ := lExponentialFamily_first_derivatives_of_lower_contact
    hM04 hτmax hwindow hL A Z b r.tau_pos r.tau_lt r.representative hB hvalue' hlow
  have hK := (regular_harnackIntegral_eq_family hM04 hwindow r A Z hpath).trans
    (lExponentialFamily_harnack_integral_eq hM04 hτmax hwindow A Z b r.tau_pos r.tau_lt)
  rw [hend] at hgrad htime hK
  constructor
  · rw [htime, hK, hvalue]
    field_simp [r.tau_pos.ne', (Real.sqrt_pos.mpr r.tau_pos).ne']
    ring
  · rw [hgrad, hK, hvalue]
    field_simp [r.tau_pos.ne', (Real.sqrt_pos.mpr r.tau_pos).ne']
    ring

end PoincareConjecture.Proofs.M09
