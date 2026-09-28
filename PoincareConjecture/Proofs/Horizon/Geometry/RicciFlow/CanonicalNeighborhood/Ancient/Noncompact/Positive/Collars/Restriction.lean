import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.Constructor
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

noncomputable def restrictNeck {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) {epsilon : ℝ} (hle : N.epsilon ≤ epsilon)
    (hhalf : epsilon < 1 / 2) : EpsilonNeck g := by
  have hpow : N.scale⁻¹ ^ 2 = N.connection.scalarCurvature N.center := by
    rw [N.scale_eq_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le,
      inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul N.scalar_center_pos.le]
    norm_num
  have hclose := roundCylinderClose_mono N.epsilon_pos hle (by norm_num : (0 : ℝ) < 1)
    N.metric_comparison.close
  rw [hpow] at hclose
  exact N.withMetric g N.connection hle hhalf N.scalar_center_pos hclose

@[simp] theorem restrictNeck_center {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) {epsilon : ℝ} (hle : N.epsilon ≤ epsilon)
    (hhalf : epsilon < 1 / 2) : (restrictNeck N hle hhalf).center = N.center := rfl

variable [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


noncomputable def restrictStrongNeck {K : AncientKappaSolution 3 M} {t delta epsilon : ℝ}
    (N : StrongEvolvingNeck K t delta) (hle : delta ≤ epsilon) (hhalf : epsilon < 1 / 2) :
    StrongEvolvingNeck K t epsilon where
  time_mem := N.time_mem
  center := N.center
  duration := N.duration
  duration_pos := N.duration_pos
  normalized_duration := N.normalized_duration
  terminal_neck := restrictNeck N.terminal_neck (N.terminal_epsilon.trans_le hle) hhalf
  terminal_center := N.terminal_center
  terminal_epsilon := rfl
  terminal_connection := N.terminal_connection
  metric_comparison := DeepHorn.roundCylinderFamilyClose_mono
    (N.terminal_epsilon ▸ N.terminal_neck.epsilon_pos) hle
    (fun _ hu => hu.2.trans_lt (by norm_num)) N.metric_comparison

@[simp] theorem restrictStrongNeck_center {K : AncientKappaSolution 3 M}
    {t delta epsilon : ℝ} (N : StrongEvolvingNeck K t delta)
    (hle : delta ≤ epsilon) (hhalf : epsilon < 1 / 2) :
    (restrictStrongNeck N hle hhalf).center = N.center := rfl

end PoincareConjecture.NoncompactKappa.Positive
