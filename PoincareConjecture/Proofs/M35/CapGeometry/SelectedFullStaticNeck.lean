import PoincareConjecture.Proofs.M35.CapGeometry.FullStaticStability
import PoincareConjecture.Proofs.M35.CapGeometry.UniformFullNeckJets
import PoincareConjecture.Proofs.M35.Thm12_28.TerminalScalarConvergence
import PoincareConjecture.Proofs.M35.Thm12_28.NeckPullbackSmoothness










set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)




theorem blowupSequence_full_static_neck_close
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (N : EpsilonNeck (L.limit.flow.metric 0)) (_he : N.epsilon ≤ 1 / 24)
      (_hconnection : N.connection = L.limit.flow.connection 0)
      (_hcompact : IsCompact (closure N.carrier))
      (j : ℕ) (_hstage : closure N.carrier ⊆ L.exhaustion.space j),
      ∀ᶠ k in atTop,
      let f (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      RoundCylinderClose N.epsilon 0 (fun z v w =>
        (E.flow.connection (t (L.subsequence k))).scalarCurvature (f N.center) *
          roundCylinderPullback (E.flow.metric (t (L.subsequence k)))
            (f ∘ N.coordinate_map) z v w) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro N he hconnection hcompact j hstage
  let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
    ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let S := N.scale⁻¹ ^ 2
  have hS : 0 < S := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hQ (k : ℕ) : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  have hscalar : S = (L.limit.flow.connection 0).scalarCurvature N.center := by
    dsimp only [S]
    rw [N.scale_eq_scalar, ← Real.rpow_neg N.scalar_center_pos.le,
      ← Real.rpow_natCast, ← Real.rpow_mul N.scalar_center_pos.le]
    norm_num
    rw [hconnection]
  let B (k : ℕ) : RoundCylinderTwoTensor := fun z v w => (S * Q (k + j)) *
    roundCylinderPullback (E.flow.metric (t (L.subsequence (k + j))))
      (F (k + j) ∘ N.coordinate_map) z v w
  let C : RoundCylinderTwoTensor := fun z v w =>
    S * roundCylinderPullback (L.limit.flow.metric 0) N.coordinate_map z v w
  let a (k : ℕ) := ((E.flow.connection (t (L.subsequence (k + j)))).scalarCurvature
    (F (k + j) N.center) / Q (k + j)) / S
  have hC : RoundCylinderClose N.epsilon 0 C := N.metric_comparison.close
  have hsmooth (k : ℕ) (A : ℝ) : RoundCylinderTensorSmoothOn N.epsilon
      (fun z v w => A * roundCylinderPullback (E.flow.metric (t (L.subsequence (k + j))))
        (F (k + j) ∘ N.coordinate_map) z v w) := by
    have htime : t (L.subsequence (k + j)) + 0 / Q (k + j) ∈
        Ico 0 E.flow.base.lifetime :=
      ((L.embedding (k + j)).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos (k + j)).le, le_rfl⟩ L.limit.base).property
    have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (F (k + j))
        (L.exhaustion.space (k + j)) :=
      (sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
        ((L.embedding (k + j)).forward_smooth 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos (k + j)).le, le_rfl⟩)
    exact roundCylinderPullback_scaled_smoothOn _ _ N.epsilon A
      (hF.comp N.coordinate_map_smooth (fun z hz =>
        L.exhaustion.space_increasing (Nat.le_add_left _ _)
          (hstage (subset_closure (N.coordinatePartialDiffeomorph.map_source hz)))))
  have ha : Tendsto a atTop (𝓝 1) := by
    have h := (blowupSequence_terminal_scalar_tendsto P E t x ht hR L N.center).div_const S
    rw [← hscalar, div_self hS.ne'] at h
    exact h.comp (tendsto_add_atTop_nat j)
  have hAt (D : RoundCylinderTwoTensor) (hD : RoundCylinderTensorSmoothOn N.epsilon D)
      (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (i j : Fin 3) :
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient D (chartAt E2 q) y i j)
        (0, s) := by
    apply (hD q i j).contDiffAt
    apply ((chartAt E2 q).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [sphere_chart_target]; trivial, hs⟩
  have hjet : ∀ r ≤ ⌊N.epsilon⁻¹⌋₊, ∀ i b : Fin 3, ∀ eta : ℝ, 0 < eta →
      ∃ K : ℕ, ∀ k ≥ K, ∀ q : UnitTwoSphere, ∀ s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
        ‖iteratedFDeriv ℝ r (fun y => roundCylinderTensorCoefficient (B k)
          (chartAt E2 q) y i b - roundCylinderTensorCoefficient C
            (chartAt E2 q) y i b) (0, s)‖ < eta := by
    intro r hr i b eta heta
    obtain ⟨K, hK⟩ := blowupSequence_full_neck_coefficient_jets_uniform P E t x ht hR L
      N he hcompact j hstage {0} isCompact_singleton (by simp) r hr i b
      (eta / S) (div_pos heta hS)
    refine ⟨K, ?_⟩
    intro k hk q s hs
    have hbase := hK (k + j) (hk.trans (Nat.le_add_right _ _)) 0 (mem_singleton 0) q s hs
    simp only [zero_div, add_zero] at hbase
    let f (y : RoundCylinderCoordinates) :=
      roundCylinderTensorCoefficient (fun z v w => Q (k + j) *
        roundCylinderPullback (E.flow.metric (t (L.subsequence (k + j))))
          (F (k + j) ∘ N.coordinate_map) z v w) (chartAt E2 q) y i b -
      roundCylinderTensorCoefficient
        (roundCylinderPullback (L.limit.flow.metric 0) N.coordinate_map) (chartAt E2 q) y i b
    have hsecond := roundCylinderPullback_scaled_smoothOn
      (L.limit.flow.metric 0) N.coordinate_map N.epsilon 1 N.coordinate_map_smooth
    simp only [one_mul] at hsecond
    have hf : ContDiffAt ℝ r f (0, s) :=
      ((hAt _ (hsmooth k (Q (k + j))) q s hs i b).sub
        (hAt _ hsecond q s hs i b)).of_le (by norm_cast; exact le_top)
    have heq : (fun y => roundCylinderTensorCoefficient (B k) (chartAt E2 q) y i b -
        roundCylinderTensorCoefficient C (chartAt E2 q) y i b) = S • f := by
      funext y
      change (S * Q (k + j)) * _ - S * _ = S * (Q (k + j) * _ - _)
      dsimp only [roundCylinderTensorCoefficient]
      ring
    rw [heq, iteratedFDeriv_const_smul_apply hf, norm_smul, Real.norm_eq_abs, abs_of_pos hS]
    simpa only [mul_comm] using (lt_div_iff₀ hS).mp hbase
  have hclose := eventually_full_static_close_of_rescaled_coefficients N.epsilon_pos hC
    B (fun k => hsmooth k (S * Q (k + j))) a ha hjet
  obtain ⟨K, hK⟩ := eventually_atTop.mp hclose
  filter_upwards [eventually_ge_atTop (K + j)] with k hk
  have hjk : j ≤ k := by omega
  have hkj : K ≤ k - j := by omega
  have h := hK (k - j) hkj
  have heq : (fun z v w => a (k - j) * B (k - j) z v w) =
      (fun z v w => (E.flow.connection (t (L.subsequence k))).scalarCurvature (F k N.center) *
        roundCylinderPullback (E.flow.metric (t (L.subsequence k)))
          (F k ∘ N.coordinate_map) z v w) := by
    funext z v w
    dsimp only [a, B]
    rw [Nat.sub_add_cancel hjk]
    field_simp [hS.ne', (hQ k).ne']
  change RoundCylinderClose N.epsilon 0 (fun z v w =>
    (E.flow.connection (t (L.subsequence k))).scalarCurvature (F k N.center) *
      roundCylinderPullback (E.flow.metric (t (L.subsequence k)))
        (F k ∘ N.coordinate_map) z v w)
  rw [← heq]
  exact h

end PoincareConjecture.M35.OrdinaryRealization
