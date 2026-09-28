import PoincareConjecture.Proofs.M30.Thm11_1.StaticRelatedNecks
import PoincareConjecture.Proofs.M30.Thm11_1.StaticStageBackwardLimit
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalBoundAssembly
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_static_limit_terminal_curvature_bound_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (_hC : RicciFlowCurvatureTheory.{u})
        {S : GeneralizedBlowupSequence.{u}}
        {epsilon canonicalConstant kappa r0 mu : ℝ}
        (_H : M30CommonBlowupControls S epsilon canonicalConstant kappa r0 mu),
        epsilon ≤ epsilon0 → GeneralizedBlowupBoundedDistance S →
      ∀ (G : PartialPointedMetricConvergence
          (terminalComponentMetric S) (terminalComponentBase S) 1),
        G.limitCarrier.metricComplete G.limitMetric →
      ∀ D : LeviCivitaData G.limitMetric,
        ∃ B : ℝ, 4 ≤ B ∧
          (∀ x : G.limitCarrier.carrier, D.scalarCurvature x ≤ B) ∧
          ∀ x : G.limitCarrier.carrier, |D.curvatureTensorNorm x| ≤ 13 * B := by
  classical
  obtain ⟨epsilonRelated, hRelatedPos, hRelatedSmall, hrelated⟩ :=
    exists_static_limit_related_neck_threshold.{u}
  obtain ⟨epsilonBound, hBoundPos, _hBoundSmall, hterminalBound⟩ :=
    exists_terminal_curvature_bound_threshold.{0, 0, 0}
  refine ⟨min epsilonRelated (epsilonBound / 2), lt_min hRelatedPos (half_pos hBoundPos),
    (min_le_left _ _).trans hRelatedSmall, ?_⟩
  intro hC S epsilon canonicalConstant kappa r0 mu H hepsilon hbound G hcomplete D
  let : ConnectedSpace G.limitCarrier.carrier :=
    connectedSpace_iff_univ.mpr G.limitCarrier.connected
  let Y (j : ℕ) : TopologicalSpace.Opens G.limitCarrier.carrier :=
    ⟨G.exhaustion j, G.exhaustion_open j⟩
  let : ∀ j, ConnectedSpace (Y j) :=
    fun j => Subtype.connectedSpace (G.exhaustion_connected j)
  let e (j : ℕ) : Y j → G.limitCarrier.carrier := Subtype.val
  have he (j : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e j) :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (Y j)
  have hstage (j : ℕ) :
      ∃ tau : ℝ, 0 < tau ∧ ∃ F : RicciFlow 3 (Y j) (Icc (-tau) 0),
        F.metric 0 = G.limitMetric.pullbackOfLocalDiffeomorph (e j) (he j) ∧
          ∀ t ∈ Icc (-tau) 0, ∀ z : Y j,
            (F.connection t).NonnegativeCurvatureOperator z :=
    exists_nonnegative_backward_flow_on_static_stage hC H hbound G hcomplete j
  choose tau htau F hterminal hoperator using hstage
  have hmetric (j : ℕ) (z : Y j) (v w : TangentSpace (𝓡 3) z) :
      ((F j).metric 0).inner z v w = G.limitMetric.inner (e j z)
        (mfderiv (𝓡 3) (𝓡 3) (e j) z v)
        (mfderiv (𝓡 3) (𝓡 3) (e j) z w) := by
    rw [hterminal j, RiemannianMetric.pullbackOfLocalDiffeomorph_inner]
  have hsign (x : G.limitCarrier.carrier) : D.NonnegativeCurvatureOperator x := by
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
      (show IsCompact ({x} : Set G.limitCarrier.carrier) from isCompact_singleton)
    let z : Y j := ⟨x, hj (mem_singleton x)⟩
    exact ((F j).connection 0).nonnegativeCurvatureOperator_iff_of_local_isometry
      D isOpen_univ (he j).contMDiff.contMDiffOn
      (fun y _ v w => hmetric j y v w) (mem_univ z) |>.mp
        (hoperator j 0 ⟨by linarith [htau j], le_rfl⟩ z)
  have hsec : D.NonnegativeSectionalCurvature :=
    fun x v w => D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x
      (hsign x) v w
  have hnonflat : D.curvatureTensorNorm G.base ≠ 0 := by
    intro hzero
    have hnorm := D.abs_scalarCurvature_le_curvatureTensorNorm_sharp G.base
    rw [terminal_static_limit_base_scalar S G D, hzero] at hnorm
    norm_num at hnorm
  have hcapture (x y : G.limitCarrier.carrier) : ∃ j,
      x ∈ range (e j) ∧ G.base ∈ range (e j) ∧ y ∈ range (e j) := by
    have hcompact : IsCompact ({x, G.base, y} : Set G.limitCarrier.carrier) :=
      (isCompact_singleton.insert G.base).insert x
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
    refine ⟨j, ⟨⟨x, hj (by simp)⟩, rfl⟩,
      ⟨⟨G.base, hj (by simp)⟩, rfl⟩, ⟨⟨y, hj (by simp)⟩, rfl⟩⟩
  have hcanonical (x : G.limitCarrier.carrier) (hx : 4 < D.scalarCurvature x) :
      (∃ N : EpsilonNeck G.limitMetric, N.epsilon = 2 * epsilon ∧
        D.scalarCurvature x ≤
          max 1 (2 * canonicalConstant) * D.scalarCurvature N.center) ∨
        IsCompact (univ : Set G.limitCarrier.carrier) := by
    rcases hrelated hC H (hepsilon.trans (min_le_left _ _)) hbound G hcomplete D x hx
      with ⟨N, hN, _hD, hratio⟩ | hcompact
    · exact Or.inl ⟨N, hN, hratio⟩
    · exact Or.inr hcompact
  have hdouble : 2 * epsilon ≤ epsilonBound := by
    have hle := hepsilon.trans (min_le_right epsilonRelated (epsilonBound / 2))
    linarith
  exact hterminalBound (ι := ℕ) (N := fun j => Y j)
    (M := G.limitCarrier.carrier) PoincareConjecture.ricciFlowCurvatureTheory.{0}
    (fun j => -tau j) (fun j => neg_neg_of_pos (htau j)) F hoperator
    D D.curvatureTensorCalculus hcomplete hsec e he hmetric G.base hnonflat hcapture
    (2 * epsilon) (2 * canonicalConstant) (mul_pos (by norm_num) H.epsilon_pos)
    hdouble hcanonical

end PoincareConjecture.M30
