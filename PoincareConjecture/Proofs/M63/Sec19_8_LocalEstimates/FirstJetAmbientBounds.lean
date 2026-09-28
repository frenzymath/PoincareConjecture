import PoincareConjecture.Proofs.M62.Cor0_3_AmbientBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63Exists_firstJet_ambient_bounds
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M)) :
    ∃ K : ℝ, 0 ≤ K ∧ CurveEvolutionAmbientBounds F K K K ∧
      (∀ t ∈ Icc a b, ∀ p : M, ∀ v : Fin 5 → TangentSpace (𝓡 n) p,
        (∀ i, (F.metric t).tangentNorm p (v i) ≤ 1) →
          |(F.connection t).covariantTensorDerivative
            (F.connection t).riemannEvaluation p v| ≤ K) ∧
      (∀ t ∈ Icc a b, ∀ p : M, ∀ v : Fin 4 → TangentSpace (𝓡 n) p,
        (∀ i, (F.metric t).tangentNorm p (v i) ≤ 1) →
          |(F.connection t).covariantTensorDerivative
            ((F.connection t).covariantTensorDerivative
              (F.connection t).ricciEvaluation) p v| ≤ K) := by
  obtain ⟨K0, K1, K2, ⟨h0, h1, h2⟩, hbounds⟩ := M62.exists_ambient_bounds F hcompact
  obtain ⟨K3, h3, hR⟩ := M62.exists_uniform_tensor_bound F hcompact
    (fun t => (F.connection t).covariantTensorDerivative (F.connection t).riemannEvaluation)
    (fun t => M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t)
      (M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t)))
    (fun U hU X hX => M04.contMDiffOn_flow_covariantTensorDerivative F
      (fun t => M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t))
      (fun V hV Y hY => M04.contMDiffOn_flow_riemannEvaluation F hV Y hY) hU hX)
  obtain ⟨K4, h4, hRic⟩ := M62.exists_uniform_tensor_bound F hcompact
    (fun t => (F.connection t).covariantTensorDerivative
      ((F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation))
    (fun t => M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t)
      (M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t)
        (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))))
    (fun U hU X hX => M04.contMDiffOn_flow_covariantTensorDerivative F
      (fun t => M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t)
        (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t)))
      (fun V hV Y hY => M04.contMDiffOn_flow_covariantTensorDerivative F
        (fun t => M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))
        (fun W hW Z hZ => M04.contMDiffOn_flow_ricciEvaluation F hW hZ) hV hY) hU hX)
  let K := K0 + K1 + K2 + K3 + K4
  have hK0 : K0 ≤ K := by dsimp only [K]; linarith
  have hK1 : K1 ≤ K := by dsimp only [K]; linarith
  have hK2 : K2 ≤ K := by dsimp only [K]; linarith
  have hK3 : K3 ≤ K := by dsimp only [K]; linarith
  have hK4 : K4 ≤ K := by dsimp only [K]; linarith
  refine ⟨K, by dsimp only [K]; positivity, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro t ht p v hv
      exact (hbounds.riemann t ht p v hv).trans hK0
    · intro t ht p v hv
      exact (hbounds.ricci_derivative t ht p v hv).trans hK1
    · intro t ht p v w hv hw
      exact (hbounds.ricci t ht p v w hv hw).trans hK2
  · intro t ht p v hv
    exact (hR t ht p v hv).trans hK3
  · intro t ht p v hv
    exact (hRic t ht p v hv).trans hK4

end PoincareConjecture
