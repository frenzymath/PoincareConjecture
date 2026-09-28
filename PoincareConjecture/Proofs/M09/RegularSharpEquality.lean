import PoincareConjecture.Proofs.M09.SharpLowerContact
import PoincareConjecture.Proofs.M09.RegularContactFormulas





set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p q : M} {b : ℝ}

set_option backward.isDefEq.respectTransparency false in
theorem regular_sharp_laplacian_tensor_eq
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (r : ReducedLengthRegularPoint F T τmax p q b)
    (hsharp : reducedLengthLaplacian F T r.representative b q =
      (n : ℝ) / (2 * b) - (F.connection (T - b)).scalarCurvature q -
        reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative b /
          (2 * b * Real.sqrt b)) :
    ∀ v w : TangentSpace (𝓡 n) q,
      (F.connection (T - b)).ricci q v w +
        (F.connection (T - b)).hessian (fun x ↦ r.representative (x, b)) q v w =
          (F.metric (T - b)).inner q v w / (2 * b) := by
  obtain ⟨Z, hpath, _⟩ := lExponentialFamily_minimizers_lift hM04 hL hτmax hwindow
    A b r.tau_pos r.tau_lt r.path r.path_start r.minimizing
  have hend : A.gamma Z b = q := (hpath ⟨r.tau_pos.le, le_rfl⟩).symm.trans r.path_end
  have hselected : Set.EqOn r.path.curve (A.path Z b r.tau_pos r.tau_lt).curve (Set.Icc 0 b) := by
    rw [A.path_eq]
    exact hpath
  have hmin := (isMinimizingBackwardLPath_iff_of_eqOn r.path
    (A.path Z b r.tau_pos r.tau_lt) hselected).mp r.minimizing
  let O : Set M := {x | (x, b) ∈ r.neighborhood}
  have hO : IsOpen O := r.neighborhood_open.preimage (continuous_id.prodMk continuous_const)
  have hqO : A.gamma Z b ∈ O := by rw [hend]; exact r.center_mem
  have hvalue : r.representative (A.gamma Z b, b) = A.action Z b / (2 * Real.sqrt b) := by
    rw [hend]
    exact regular_representative_eq_family_action r A Z hpath
  have hlow : ∀ᶠ x in 𝓝 (A.gamma Z b), r.representative (x, b) ≤ reducedLength F T p x b := by
    filter_upwards [hO.mem_nhds hqO] with x hx
    exact (r.representative_eq (x, b) hx).le
  have hsharp' : (F.connection (T - b)).laplacian (fun x ↦ r.representative (x, b)) (A.gamma Z b) =
      (n : ℝ) / (2 * b) - (F.connection (T - b)).scalarCurvature (A.gamma Z b) -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / (2 * b * Real.sqrt b) := by
    rw [hend, ← regular_harnackIntegral_eq_family hM04 hwindow r A Z hpath]
    exact hsharp
  have h := lExponentialFamily_tensor_eq_of_sharp_lower_contact hM04 hL hτmax hwindow
    A Z b r.tau_pos r.tau_lt hmin (fun x ↦ r.representative (x, b)) O hO hqO
      r.representative_space_smooth_on hvalue hlow hsharp'
  rwa [hend] at h

end PoincareConjecture.Proofs.M09
