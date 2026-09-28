import PoincareConjecture.Proofs.M28.Sec10_3_Tube.TubeRegionMinimizers
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RecenteredCompetitor
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.EndpointScalarSeparation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28




theorem exists_tube_source_minimizer_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (X : Set M) (T : EpsilonTubeCertificate g X),
        T.epsilon ≤ epsilon₀ →
        ∀ (C Q A : ℝ) (η : ℝ → M) (a b : ℝ), 0 < Q → a ≤ b →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b) →
          MapsTo η (Icc a b) T.carrier →
          g.pathELength η a b < ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) →
          D.scalarCurvature (η a) = 8 * Q →
          32 * (max C 2) ^ 4 * Q < D.scalarCurvature (η b) →
          ∃ i ∈ T.chain.shape.active, ∃ j ∈ T.chain.shape.active,
            ∃ γ : ℝ → M, γ 0 = (T.chain.neck i).center ∧
              γ 1 = (T.chain.neck j).center ∧
              D.scalarCurvature (γ 0) ≤ 8 * max C 2 * Q ∧
              32 * (max C 2) ^ 3 * Q < D.scalarCurvature (γ 1) ∧
              D.scalarCurvature (η b) ≤ max C 2 * D.scalarCurvature (γ 1) ∧
              ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
              MapsTo γ (Icc (0 : ℝ) 1) T.carrier ∧
              g.pathELength γ 0 1 = intrinsicEDist g T.carrier (γ 0) (γ 1) ∧
              g.pathELength γ 0 1 ≠ ⊤ ∧
              g.pathELength γ 0 1 <
                ENNReal.ofReal ((A + 2 * endpointConnectorBudget T.epsilon C) *
                  Q ^ (-1 / 2 : ℝ)) := by
  obtain ⟨epsilonR, hRpos, hRthreshold, hrecentering⟩ :=
    exists_neck_endpoint_recentering_accuracy.{u}
  obtain ⟨epsilonS, hSpos, _, hseparation⟩ :=
    exists_endpoint_scalar_separation_accuracy.{u}
  let epsilon₀ := min epsilonR (min epsilonS neckShorteningEpsilon)
  refine ⟨epsilon₀, lt_min hRpos (lt_min hSpos neckShorteningEpsilon_pos),
    (min_le_left _ _).trans hRthreshold, ?_⟩
  intro M _ _ _ _ _ _ _ g D X T hsmall C Q A η a b hQ hab hη hηU hηL hz hy
  have hsmallR : T.epsilon ≤ epsilonR := hsmall.trans (min_le_left _ _)
  have hsmallS : T.epsilon ≤ epsilonS :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hshort : T.epsilon ≤ neckShorteningEpsilon :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpa := hηU (left_mem_Icc.mpr hab)
  have hpb := hηU (right_mem_Icc.mpr hab)
  rw [T.carrier_eq_chain_union] at hpa hpb
  obtain ⟨i, hpi⟩ := mem_iUnion.mp hpa
  obtain ⟨j, hpj⟩ := mem_iUnion.mp hpb
  have hNi : (T.chain.neck i.val).carrier ⊆ T.carrier := by
    rw [T.carrier_eq_chain_union]
    exact subset_iUnion_of_subset i Subset.rfl
  have hNj : (T.chain.neck j.val).carrier ⊆ T.carrier := by
    rw [T.carrier_eq_chain_union]
    exact subset_iUnion_of_subset j Subset.rfl
  have hiepsilon := T.chain.epsilon_eq i.val i.property
  have hjepsilon := T.chain.epsilon_eq j.val j.property
  have hdisj := (hseparation M g D C Q (η a) (η b) hQ hz hy).1
    (T.chain.neck i.val) (T.chain.neck j.val)
    (hiepsilon.trans_le hsmallS) (hjepsilon.trans_le hsmallS) hpi hpj
  obtain ⟨_, _, _, _, hlow, _, _, α, hα0, hα1, hα, hαN, hαL⟩ :=
    hrecentering T.epsilon C T.epsilon_pos hsmallR M g D
      (T.chain.neck i.val) Q (η a) hQ hiepsilon hpi (Or.inl hz)
  obtain ⟨_, _, hcomparison, _, _, hhigh, hforward, _⟩ :=
    hrecentering T.epsilon C T.epsilon_pos hsmallR M g D
      (T.chain.neck j.val) Q (η b) hQ hjepsilon hpj (Or.inr hy)
  obtain ⟨β, hβ0, hβ1, hβ, hβN, hβL⟩ := hforward
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσL⟩ :=
    exists_recentered_competitor_of_connectors g T.epsilon_pos hQ hab hη hηU hηL
      hα0 hα1 hα (fun t ht => hNi (hαN ht)) hαL
      hβ0 hβ1 hβ (fun t ht => hNj (hβN ht)) hβL
  obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγmin, hγfinite, hγL⟩ :=
    T.exists_chain_neck_minimizer i.val j.val i.property j.property hdisj hshort
      zero_le_one hσ hσU (hσ0 ▸ (T.chain.neck i.val).center_on_central_sphere)
      (hσ1 ▸ (T.chain.neck j.val).center_on_central_sphere) hσL
  refine ⟨i.val, i.property, j.val, j.property, γ, hγ0.trans hσ0, hγ1.trans hσ1,
    ?_, ?_, ?_, hγ, hγU, ?_, hγfinite, hγL⟩
  · simpa only [hγ0, hσ0] using hlow hz
  · simpa only [hγ1, hσ1] using hhigh hy
  · simpa only [hγ1, hσ1] using hcomparison
  · simpa only [hγ0, hγ1] using hγmin

end PoincareConjecture.M28
