import PoincareConjecture.Proofs.M47.BlowupControlsSourceHistory
import PoincareConjecture.Proofs.M47.TerminalSourceRealization
import PoincareConjecture.Proofs.M47.BlowupControlsCylinderDerivative
import PoincareConjecture.Proofs.M04.ShiCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {base A K tau0 tau : ℝ}
  (hbase : base ∈ H.generalized.interval)
  (x : (H.generalized.slice base).carrier)

local notation "Q" => H.generalized.scalar (Sigma.mk base x)
local notation "U" => (TopologicalSpace.Opens.mk
  (RiemannianMetric.ball (F.metric base) (H.history.forward base hbase x) (A / Real.sqrt Q))
  (M04.initial_ball_isOpen _ _ _))

theorem terminalSource_realize_regular_stage
    (P : M47Predecessors.{u}) (hA : 0 < A) (htau : 0 < tau) (htt : tau < tau0)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau0) 0) U)
    (hbased : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hbound : ∀ s hs y, y ∈ U →
      (F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs y) ≤ K * Q) :
    ∃ p0 : U, p0.val = H.history.forward base hbase x ∧
      ∃ htime : ∀ s ∈ Icc (-tau) 0, base + s / Q ∈ H.generalized.interval,
      ∃ d : GeneralizedFlowCylinder H.generalized (F.slice base) base Q
          (Icc (-tau) 0) U,
      ∃ G : RicciFlow 3 U (Icc (-tau) 0),
        (∀ s hs y, y ∈ U → H.history.forward (base + s / Q) (htime s hs)
          (d.forward s hs y) = e.forward s ⟨(neg_lt_neg htt).le.trans hs.1, hs.2⟩ y) ∧
        (∀ s hs y, y ∈ U → ∀ v w : TangentSpace (𝓡 3) y,
          d.pullbackInner s hs y v w =
            e.pullbackInner s ⟨(neg_lt_neg htt).le.trans hs.1, hs.2⟩ y v w) ∧
        (∀ (s : ℝ) (hs : s ∈ Icc (-tau) 0) (z : U),
          (∀ v w : TangentSpace (𝓡 3) z,
            (G.metric s).inner z v w = d.pullbackInner s hs z.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z w)) ∧
          (G.connection s).scalarCurvature z =
            (H.generalized.connection (base + s / Q)).scalarCurvature
              (d.forward s hs z.val) / Q ∧
          (G.connection s).curvatureTensorNorm z =
            (H.generalized.connection (base + s / Q)).curvatureTensorNorm
              (d.forward s hs z.val) / Q) ∧
        (∀ (s : ℝ) (hs : s ∈ Icc (-tau) 0) (z : U),
          (G.connection s).scalarCurvature z =
            (F.connection (base + s / Q)).scalarCurvature
              (e.forward s ⟨(neg_lt_neg htt).le.trans hs.1, hs.2⟩ z.val) / Q ∧
          (G.connection s).curvatureTensorNorm z =
            (F.connection (base + s / Q)).curvatureTensorNorm
              (e.forward s ⟨(neg_lt_neg htt).le.trans hs.1, hs.2⟩ z.val) / Q) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : U, (G.connection s).curvatureTensorNorm z ≤ K) ∧
        (∀ z : U, (G.connection 0).scalarCurvature z =
          (F.connection base).scalarCurvature z.val / Q) ∧
        (G.connection 0).scalarCurvature p0 = 1 ∧
        (∀ y, y ∈ U → normalizedCylinderScalar d y 0 ≤ 9 * K) ∧
        let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
        let j := terminalSourceNormal_terminalMap U p0
          (terminalSourceNormal_historyCylinder H U htime d) h0
        j.source = univ ∧ j.target = U ∧ (∀ z : U, j z = z.val) := by
  have hcenter : H.history.forward base hbase x ∈ U := by
    change (F.metric base).edist _ _ < ENNReal.ofReal (A / Real.sqrt Q)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hA (Real.sqrt_pos.mpr e.scale_pos))
  let p0 : U := ⟨H.history.forward base hbase x, hcenter⟩
  obtain ⟨htime, d, hmaps, hmetric, hterminal⟩ :=
    exists_regular_history_search_interior H hbase htau (neg_lt_neg htt) U p0 e hbased
  obtain ⟨G, hG⟩ := terminalSourceRealization_generalized P htau U ⟨p0, p0.property⟩ d
  have hphysical (s : ℝ) (hs : s ∈ Icc (-tau) 0) (z : U) :
      (G.connection s).scalarCurvature z =
          (F.connection (base + s / Q)).scalarCurvature
            (e.forward s ⟨(neg_lt_neg htt).le.trans hs.1, hs.2⟩ z.val) / Q ∧
        (G.connection s).curvatureTensorNorm z =
          (F.connection (base + s / Q)).curvatureTensorNorm
            (e.forward s ⟨(neg_lt_neg htt).le.trans hs.1, hs.2⟩ z.val) / Q := by
    constructor
    · rw [(hG s hs z).2.1, ← H.scalar_pullback _ (htime s hs), hmaps s hs z.val z.property]
    · rw [(hG s hs z).2.2, ← H.curvature_norm_pullback _ (htime s hs),
        hmaps s hs z.val z.property]
  have hnorm (s : ℝ) (hs : s ∈ Icc (-tau) 0) (z : U) :
      (G.connection s).curvatureTensorNorm z ≤ K := by
    rw [(hphysical s hs z).2]
    exact (div_le_iff₀ e.scale_pos).mpr (hbound s _ z.val z.property)
  let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
  have hscalar (z : U) : (G.connection 0).scalarCurvature z =
      (F.connection base).scalarCurvature z.val / Q := by
    have he : (⟨base + 0 / Q,
        e.forward 0 ⟨(neg_lt_neg htt).le.trans h0.1, h0.2⟩ z.val⟩ :
          Σ t, (F.slice t).carrier) = ⟨base, z.val⟩ :=
      Sigma.ext (by simp) (hbased _ z.val z.property)
    have hr := congrArg (fun p : Σ t, (F.slice t).carrier =>
      (F.connection p.1).scalarCurvature p.2) he
    have hrQ := congrArg (fun a : ℝ => a / Q) hr
    exact (hphysical 0 h0 z).1.trans hrQ
  refine ⟨p0, rfl, htime, d, G, hmaps, hmetric, hG, hphysical, hnorm, hscalar, ?_, ?_, ?_⟩
  · rw [hscalar p0]
    change (F.connection base).scalarCurvature (H.history.forward base hbase x) / Q = 1
    rw [H.scalar_pullback base hbase x]
    exact div_self e.scale_pos.ne'
  · intro y hy
    have hread := (hG 0 h0 ⟨y, hy⟩).2.1
    have hnormScalar : normalizedCylinderScalar d y 0 =
        (G.connection 0).scalarCurvature ⟨y, hy⟩ := by
      rw [normalizedCylinderScalar, dif_pos h0]
      exact hread.symm
    rw [hnormScalar]
    have hs := (G.connection 0).abs_scalarCurvature_le_curvatureTensorNorm (⟨y, hy⟩ : U)
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_two] at hs
    exact (le_abs_self _).trans (hs.trans (mul_le_mul_of_nonneg_left (hnorm 0 h0 _) (by norm_num)))
  · have hj := terminalSourceNormal_terminal_map U p0
      (terminalSourceNormal_historyCylinder H U htime d) h0
    exact ⟨hj.1, hj.2.1.trans hterminal.2, hterminal.1⟩

end PoincareConjecture.M47
