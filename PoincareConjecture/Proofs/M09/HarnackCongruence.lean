import PoincareConjecture.Proofs.M09.HarnackIntegrability
import PoincareConjecture.Proofs.M09.ActionCongruence









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem weightedHarnackIntegral_congr_Ioo {J : Set ℝ} (F : RicciFlow n M J)
    (T a b : ℝ) (hab : a ≤ b) (γ δ : ℝ → M) (d e : ℝ → ℝ)
    (heq : Set.EqOn γ δ (Set.Ioo a b)) (hde : Set.EqOn d e (Set.Ioo a b)) :
    (∫ t in a..b, t * Real.sqrt t * reducedHarnackDensity F T γ d t) =
      ∫ t in a..b, t * Real.sqrt t * reducedHarnackDensity F T δ e t := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  have hlocal : γ =ᶠ[nhds t] δ := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) heq
  have hderiv := hlocal.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  have hv : (curveVelocity (n := n) γ t : EuclideanSpace ℝ (Fin n)) =
      curveVelocity (n := n) δ t :=
    congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L 1) hderiv
  have hphase : (⟨γ t, curveVelocity (n := n) γ t⟩ : TangentBundle (𝓡 n) M) =
      ⟨δ t, curveVelocity (n := n) δ t⟩ :=
    Bundle.TotalSpace.ext (heq ht) (heq_of_eq hv)
  have hvalue := congrArg (fun q : TangentBundle (𝓡 n) M ↦
    -e t - (F.connection (T - t)).scalarCurvature q.1 / t -
      2 * mvfderiv (𝓡 n) (F.connection (T - t)).scalarCurvature q.1 q.2 +
      2 * (F.connection (T - t)).ricci q.1 q.2 q.2) hphase
  unfold reducedHarnackDensity
  dsimp only
  rw [hde ht]
  exact congrArg (fun v : ℝ ↦ t * Real.sqrt t * v) hvalue

theorem regular_harnackIntegral_eq_family {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax b : ℝ}
    (hwindow : Set.Icc (T - τmax) T ⊆ J) {p q : M}
    (r : ReducedLengthRegularPoint F T τmax p q b)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (heq : Set.EqOn r.path.curve (A.gamma Z) (Set.Icc 0 b)) :
    reducedHarnackIntegral F T r.path.curve r.path_scalar_time_derivative b =
      reducedHarnackIntegral F T (A.gamma Z) (backwardScalarEvolutionAlong F T (A.gamma Z)) b := by
  apply weightedHarnackIntegral_congr_Ioo F T 0 b r.tau_pos.le _ _ _ _
    (heq.mono Set.Ioo_subset_Icc_self)
  intro t ht
  rw [regular_scalar_derivative_eq hM04 hwindow r ht, heq (Set.Ioo_subset_Icc_self ht)]
  rfl

theorem regular_representative_eq_family_action {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax b : ℝ} {p q : M} (r : ReducedLengthRegularPoint F T τmax p q b)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (heq : Set.EqOn r.path.curve (A.gamma Z) (Set.Icc 0 b)) :
    r.representative (q, b) = A.action Z b / (2 * Real.sqrt b) := by
  rw [r.representative_eq (q, b) r.center_mem, r.path_realizes_reduced_length]
  exact congrArg (fun a : ℝ ↦ a / (2 * Real.sqrt b))
    (backwardLLength_congr_Ioo F T 0 b r.tau_pos.le _ _ (heq.mono Set.Ioo_subset_Icc_self))

end PoincareConjecture.Proofs.M09
