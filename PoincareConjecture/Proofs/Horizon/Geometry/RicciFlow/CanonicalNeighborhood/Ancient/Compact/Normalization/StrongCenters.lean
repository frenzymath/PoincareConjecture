import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.StrongNeck











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaNormalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M} {b epsilon : ℝ}

private theorem inverse_scalar_scale_sq {R : ℝ} (hR : 0 < R) :
    (R ^ (-1 / 2 : ℝ))⁻¹ ^ 2 = R := by
  rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le]
  norm_num


def terminalNeckAtCenterFromNormalization
    (A : AncientKappaNormalization K p b)
    (N : StrongEvolvingNeck A.target 0 epsilon) :
    EpsilonNeck (K.flow.metric b) := by
  let R := (K.flow.connection b).scalarCurvature N.center
  have hscalar : (A.target.flow.connection 0).scalarCurvature N.center =
      R / A.scale := by rw [A.scalar_eq 0 le_rfl, zero_div, add_zero]
  have htarget : 0 < (A.target.flow.connection 0).scalarCurvature N.center := by
    simpa only [N.terminal_connection, N.terminal_center] using N.terminal_neck.scalar_center_pos
  have hR : 0 < R := (div_pos_iff_of_pos_right A.scale_pos).mp (hscalar ▸ htarget)
  refine {
    N.terminal_neck with
    scale := R ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := N.center
    connection := K.flow.connection b
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    center_on_central_sphere := by
      simpa only [N.terminal_center] using N.terminal_neck.center_on_central_sphere
    metric_comparison := ⟨?_⟩ }
  have hclose := N.terminal_neck.metric_comparison.close
  rw [N.terminal_neck.scale_eq_scalar, N.terminal_connection, N.terminal_center,
    inverse_scalar_scale_sq htarget, hscalar] at hclose
  convert hclose using 1
  funext z v w
  rw [inverse_scalar_scale_sq hR]
  change R * (K.flow.metric b).inner _ _ _ =
    (R / A.scale) * (A.target.flow.metric 0).inner _ _ _
  rw [A.metric_eq, zero_div, add_zero]
  field_simp [A.scale_pos.ne']


def strongNeckAtCenterFromNormalization
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : StrongEvolvingNeck A.target 0 epsilon) : StrongEvolvingNeck K b epsilon := by
  let R := (K.flow.connection b).scalarCurvature N.center
  have hscalar : (A.target.flow.connection 0).scalarCurvature N.center =
      R / A.scale := by rw [A.scalar_eq 0 le_rfl, zero_div, add_zero]
  have htarget : 0 < (A.target.flow.connection 0).scalarCurvature N.center := by
    simpa only [N.terminal_connection, N.terminal_center] using N.terminal_neck.scalar_center_pos
  have hR : 0 < R := (div_pos_iff_of_pos_right A.scale_pos).mp (hscalar ▸ htarget)
  refine {
    time_mem := hb
    center := N.center
    duration := R⁻¹
    duration_pos := inv_pos.mpr hR
    normalized_duration := inv_mul_cancel₀ hR.ne'
    terminal_neck := A.terminalNeckAtCenterFromNormalization N
    terminal_center := rfl
    terminal_epsilon := N.terminal_epsilon
    terminal_connection := rfl
    metric_comparison := ?_ }
  have hclose := N.metric_comparison
  rw [hscalar] at hclose
  convert hclose using 1
  funext s z v w
  change R * (K.flow.metric (b + s / R)).inner _ _ _ =
    (R / A.scale) * (A.target.flow.metric (0 + s / (R / A.scale))).inner _ _ _
  rw [A.metric_eq, zero_add]
  have ht : s / (R / A.scale) / A.scale = s / R := by field_simp [A.scale_pos.ne']
  rw [ht]
  field_simp [A.scale_pos.ne']
  rfl

@[simp] theorem strongNeckAtCenterFromNormalization_center
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : StrongEvolvingNeck A.target 0 epsilon) :
    (A.strongNeckAtCenterFromNormalization hb N).center = N.center := rfl


theorem strongNeck_coverage_fromNormalization
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0) {X : Set M}
    (hX : ∀ x ∈ X, ∃ N : StrongEvolvingNeck A.target 0 epsilon, N.center = x) :
    ∀ x ∈ X, ∃ N : StrongEvolvingNeck K b epsilon, N.center = x := by
  intro x hx
  obtain ⟨N, hN⟩ := hX x hx
  exact ⟨A.strongNeckAtCenterFromNormalization hb N, hN⟩

end PoincareConjecture.AncientKappaNormalization
