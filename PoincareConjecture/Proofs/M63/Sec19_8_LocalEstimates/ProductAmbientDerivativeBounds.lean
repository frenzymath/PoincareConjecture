import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ProductTensorDerivatives
import PoincareConjecture.Proofs.M62.Cor0_3_AmbientBounds
import PoincareConjecture.Proofs.M04.FlowRiemannRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m63CircleProduct_uniform_curvature_derivative_bounds
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M)) :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ (circumference : ℝ) (P : M62.CircleProductData F circumference),
      ∀ (m : ℕ) (t : ℝ), t ∈ Icc a b → ∀ q : P.charts.Point,
        (∀ v : Fin (4 + m) → TangentSpace (𝓡 (n + 1)) q,
          (∀ j, (P.flow.metric t).tangentNorm q (v j) ≤ 1) →
          |(P.flow.connection t).iteratedCovariantTensorDerivative
            (P.flow.connection t).riemannEvaluation m q v| ≤ K m) ∧
        (∀ v : Fin (2 + m) → TangentSpace (𝓡 (n + 1)) q,
          (∀ j, (P.flow.metric t).tangentNorm q (v j) ≤ 1) →
          |(P.flow.connection t).iteratedCovariantTensorDerivative
            (P.flow.connection t).ricciEvaluation m q v| ≤ K m) := by
  classical
  have hsmooth {k : ℕ} (t : ℝ) (T : CovariantTensorEvaluation n M k)
      (hT : IsSmoothCovariantTensor T) (m : ℕ) :
      IsSmoothCovariantTensor ((F.connection t).iteratedCovariantTensorDerivative T m) := by
    induction m with
    | zero => exact hT
    | succ m ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t) ih
  have hbounds (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x : M,
      (∀ v : Fin (4 + m) → TangentSpace (𝓡 n) x,
        (∀ j, (F.metric t).tangentNorm x (v j) ≤ 1) →
        |(F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).riemannEvaluation m x v| ≤ K) ∧
      (∀ v : Fin (2 + m) → TangentSpace (𝓡 n) x,
        (∀ j, (F.metric t).tangentNorm x (v j) ≤ 1) →
        |(F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).ricciEvaluation m x v| ≤ K) := by
    obtain ⟨KR, hKR, hR⟩ := M62.exists_uniform_tensor_bound F hcompact
      (fun t => (F.connection t).iteratedCovariantTensorDerivative
        (F.connection t).riemannEvaluation m)
      (fun t => hsmooth t _ (M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t)) m)
      (fun U hU X hX => M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F
        (fun t => M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t))
        (fun V hV Y hY => M04.contMDiffOn_flow_riemannEvaluation F hV Y hY) m hU hX)
    obtain ⟨KC, _hKC, hC⟩ := M62.exists_uniform_tensor_bound F hcompact
      (fun t => (F.connection t).iteratedCovariantTensorDerivative
        (F.connection t).ricciEvaluation m)
      (fun t => hsmooth t _ (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t)) m)
      (fun U hU X hX => M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F
        (fun t => M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))
        (fun V hV Y hY => M04.contMDiffOn_flow_ricciEvaluation F hV hY) m hU hX)
    refine ⟨max KR KC, hKR.trans (le_max_left _ _), ?_⟩
    intro t ht x
    exact ⟨fun v hv => (hR t ht x v hv).trans (le_max_left _ _),
      fun v hv => (hC t ht x v hv).trans (le_max_right _ _)⟩
  choose K hK hbound using hbounds
  refine ⟨K, hK, ?_⟩
  intro circumference P m t ht q
  let := P.charts.chartedSpace
  have hnorm (V : TangentSpace (𝓡 (n + 1)) q) :
      (F.metric t).tangentNorm q.1 (P.charts.split q V).1 ≤
        (P.flow.metric t).tangentNorm q V := by
    apply Real.sqrt_le_sqrt
    rw [P.metric_eq]
    have hc : 0 ≤ P.circle.metricOnPoints.inner q.2
        (P.charts.split q V).2 (P.charts.split q V).2 := by
      by_cases hz : (P.charts.split q V).2 = 0
      · simp only [hz, map_zero, le_refl]
      · exact (P.circle.metricOnPoints.pos q.2 _ hz).le
    exact le_add_of_nonneg_right hc
  constructor
  · intro v hv
    have hprojection := m63CircleProduct_iteratedCovariantTensorDerivative
      (F.metric t) (F.connection t) P.circle P.charts
      (P.flow.metric t) (P.flow.connection t) (P.metric_eq t)
      (F.connection t).riemannEvaluation (P.flow.connection t).riemannEvaluation
      (M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t))
      (M04.isSmoothCovariantTensor_riemannEvaluation (P.flow.connection t))
      (fun y w => M62.circleProduct_curvatureTensor
        (F.metric t) (F.connection t) P.circle P.charts
        (P.flow.metric t) (P.flow.connection t) (P.metric_eq t) y (w 0) (w 1) (w 2) (w 3))
      m q v
    rw [hprojection]
    exact (hbound m t ht q.1).1 _ (fun j => (hnorm (v j)).trans (hv j))
  · intro v hv
    have hprojection := m63CircleProduct_iteratedCovariantTensorDerivative
      (F.metric t) (F.connection t) P.circle P.charts
      (P.flow.metric t) (P.flow.connection t) (P.metric_eq t)
      (F.connection t).ricciEvaluation (P.flow.connection t).ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))
      (M04.isSmoothCovariantTensor_ricciEvaluation (P.flow.connection t))
      (fun y w => M62.circleProduct_ricci
        (F.metric t) (F.connection t) P.circle P.charts
        (P.flow.metric t) (P.flow.connection t) (P.metric_eq t) y (w 0) (w 1))
      m q v
    rw [hprojection]
    exact (hbound m t ht q.1).2 _ (fun j => (hnorm (v j)).trans (hv j))

end PoincareConjecture
