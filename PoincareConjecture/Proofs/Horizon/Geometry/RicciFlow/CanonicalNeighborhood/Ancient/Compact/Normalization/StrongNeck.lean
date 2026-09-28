import PoincareConjecture.Statements.M26CanonicalNeighborhoods









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


def terminalNeckFromNormalization
    (A : AncientKappaNormalization K p b)
    (N : StrongEvolvingNeck A.target 0 epsilon) (hcenter : N.center = p) :
    EpsilonNeck (K.flow.metric b) := by
  let R := (K.flow.connection b).scalarCurvature p
  have hR : 0 < R := by simpa only [R, A.scale_eq] using A.scale_pos
  have hNcenter : N.terminal_neck.center = p := N.terminal_center.trans hcenter
  have hNscale : N.terminal_neck.scale = 1 := by
    rw [N.terminal_neck.scale_eq_scalar, N.terminal_connection, hNcenter,
      A.normalized_scalar, Real.one_rpow]
  have hscale : (R ^ (-1 / 2 : ℝ))⁻¹ ^ 2 = R := by
    rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le]
    norm_num
  refine {
    N.terminal_neck with
    scale := R ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := p
    connection := K.flow.connection b
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    center_on_central_sphere := by
      exact (congrArg (fun x : M => x ∈ N.terminal_neck.central_sphere) hNcenter).mp
        N.terminal_neck.center_on_central_sphere
    metric_comparison := ⟨?_⟩
  }
  have hclose := N.terminal_neck.metric_comparison.close
  rw [hNscale] at hclose
  simp only [inv_one, one_pow, one_mul] at hclose
  convert hclose using 1
  funext z v w
  rw [hscale]
  change R * (K.flow.metric b).inner _ _ _ = (A.target.flow.metric 0).inner _ _ _
  rw [A.metric_eq, zero_div, add_zero, A.scale_eq]


def strongNeckFromNormalization
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : StrongEvolvingNeck A.target 0 epsilon) (hcenter : N.center = p) :
    StrongEvolvingNeck K b epsilon := by
  refine {
    time_mem := hb
    center := p
    duration := A.scale⁻¹
    duration_pos := inv_pos.mpr A.scale_pos
    normalized_duration := by rw [← A.scale_eq, inv_mul_cancel₀ A.scale_pos.ne']
    terminal_neck := A.terminalNeckFromNormalization N hcenter
    terminal_center := rfl
    terminal_epsilon := N.terminal_epsilon
    terminal_connection := rfl
    metric_comparison := ?_
  }
  have hclose := N.metric_comparison
  rw [hcenter, A.normalized_scalar] at hclose
  simp only [div_one, zero_add, one_mul] at hclose
  convert hclose using 1
  funext s z v w
  change (K.flow.connection b).scalarCurvature p *
    (K.flow.metric (b + s / (K.flow.connection b).scalarCurvature p)).inner _ _ _ =
      (A.target.flow.metric s).inner _ _ _
  rw [A.metric_eq, A.scale_eq]
  rfl


theorem exists_strongNeck_of_normalization
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (hneck : ∃ N : StrongEvolvingNeck A.target 0 epsilon, N.center = p) :
    ∃ N : StrongEvolvingNeck K b epsilon, N.center = p := by
  obtain ⟨N, hN⟩ := hneck
  exact ⟨A.strongNeckFromNormalization hb N hN, rfl⟩

end PoincareConjecture.AncientKappaNormalization
