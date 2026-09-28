import PoincareConjecture.Proofs.M47.LimitCanonicalNeckPhysicalJets
import PoincareConjecture.Proofs.M47.LimitCanonicalCapAnalytics
import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckNormalization
import PoincareConjecture.Proofs.M34.Standard.CapIsometryPullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitCanonical_eventually_neck_normalized_comparison
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (N : EpsilonNeck (G.limit.flow.metric 0))
    (hconnection : N.connection = G.limit.flow.connection 0)
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K) (hNK : N.carrier ⊆ K) :
    ∀ᶠ k in atTop,
      let f := limitCanonicalPhysicalTerminalChart G F R k
      let g := M13.scaleSmoothMetric
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      let D := M13.scaleLeviCivitaData
        ((F (G.subsequence k)).connection
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      K ⊆ G.exhaustion.space k ∧ 0 < D.scalarCurvature (f N.center) ∧
        RoundCylinderClose N.epsilon 0 (fun z v w =>
          D.scalarCurvature (f N.center) *
            roundCylinderPullback g (f ∘ N.coordinate_map) z v w) := by
  let D0 : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
    roundCylinderPullback (G.limit.flow.metric 0) N.coordinate_map z v w
  obtain ⟨rho, hrho, sigma, hsigma, hsigmaHalf, hnormalize⟩ :=
    exists_cap_neck_normalization_tolerance N.epsilon_pos D0 N.metric_comparison.close
  let eta := sigma / N.scale ^ 2
  have heta : 0 < eta := div_pos hsigma (sq_pos_of_pos N.scale_pos)
  filter_upwards [limitCanonical_eventually_physical_neck_metric_jets G P F R N hK hNK hrho,
    limitCanonical_cap_eventually_compact_analytics G P F R hK heta] with k hj ha
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let g := M13.scaleSmoothMetric
    ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let D := M13.scaleLeviCivitaData
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let B : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
    roundCylinderPullback g (f ∘ N.coordinate_map) z v w
  let beta := N.scale ^ 2 * D.scalarCurvature (f N.center)
  have hcenter : N.center ∈ K := hNK (N.central_sphere_subset N.center_on_central_sphere)
  have hscalar : |D.scalarCurvature (f N.center) -
      N.connection.scalarCurvature N.center| ≤ eta := by
    rw [hconnection]
    exact (norm_fst_le _).trans (ha.2 N.center hcenter)
  have hnormal : N.scale ^ 2 * N.connection.scalarCurvature N.center = 1 := by
    rw [N.scale_eq_scalar, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg N.scalar_center_pos.le, ← Real.sqrt_eq_rpow, inv_pow,
      Real.sq_sqrt N.scalar_center_pos.le, inv_mul_cancel₀ N.scalar_center_pos.ne']
  have hbeta : |beta - 1| ≤ sigma := by
    have heq : beta - 1 = N.scale ^ 2 *
        (D.scalarCurvature (f N.center) - N.connection.scalarCurvature N.center) := by
      dsimp only [beta]
      rw [mul_sub, hnormal]
    rw [heq, abs_mul, abs_of_pos (sq_pos_of_pos N.scale_pos)]
    apply (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _)).trans_eq
    dsimp only [eta]
    field_simp [N.scale_pos.ne']
  have hbetaPos : 0 < beta := by
    have h := (abs_le.mp (hbeta.trans hsigmaHalf)).1
    linarith
  have hR : 0 < D.scalarCurvature (f N.center) :=
    (mul_pos_iff_of_pos_left (sq_pos_of_pos N.scale_pos)).mp hbetaPos
  have hclose : RoundCylinderClose N.epsilon 0 (fun z v w => beta * B z v w) :=
    hnormalize B hj.2.1 hj.2.2 beta hbeta
  refine ⟨hj.1, hR, hclose.congr_cylinder ?_⟩
  intro z _ v w
  change (N.scale ^ 2 * D.scalarCurvature (f N.center)) *
    (N.scale⁻¹ ^ 2 * roundCylinderPullback g (f ∘ N.coordinate_map) z v w) =
      D.scalarCurvature (f N.center) * roundCylinderPullback g (f ∘ N.coordinate_map) z v w
  field_simp [N.scale_pos.ne']

end PoincareConjecture.M47
