import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CappedRegionMinimizers
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RecenteredCompetitor
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.EndpointScalarSeparation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28





theorem exists_low_cap_high_neck_source_minimizer_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (T : CappedTubeCertificate g),
        T.tube.epsilon ≤ epsilon₀ →
        ∀ (C Q A : ℝ) (η : ℝ → M) (a b : ℝ),
          T.cap.cap_constant ≤ C → 0 < Q → a ≤ b →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b) →
          MapsTo η (Icc a b) T.carrier →
          η a ∈ T.cap.carrier → η b ∈ T.tube.carrier →
          g.pathELength η a b < ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) →
          D.scalarCurvature (η a) = 8 * Q →
          32 * (max C 2) ^ 4 * Q < D.scalarCurvature (η b) →
          ∃ c ∈ T.cap.core, ∃ j ∈ T.tube.chain.shape.active,
            ∃ γ : ℝ → M, γ 0 = c ∧
              γ 1 = (T.tube.chain.neck j).center ∧
              D.scalarCurvature (γ 0) ≤ 8 * max C 2 * Q ∧
              32 * (max C 2) ^ 3 * Q < D.scalarCurvature (γ 1) ∧
              D.scalarCurvature (η b) ≤ max C 2 * D.scalarCurvature (γ 1) ∧
              ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
              MapsTo γ (Icc (0 : ℝ) 1) T.carrier ∧
              g.pathELength γ 0 1 = intrinsicEDist g T.carrier (γ 0) (γ 1) ∧
              g.pathELength γ 0 1 ≠ ⊤ ∧
              g.pathELength γ 0 1 <
                ENNReal.ofReal ((A + 2 * endpointConnectorBudget T.tube.epsilon C) *
                  Q ^ (-1 / 2 : ℝ)) := by
  obtain ⟨epsilonR, hRpos, hRthreshold, hrecentering⟩ :=
    exists_neck_endpoint_recentering_accuracy.{u}
  obtain ⟨epsilonS, hSpos, _, hseparation⟩ :=
    exists_endpoint_scalar_separation_accuracy.{u}
  let epsilon₀ := min epsilonR (min epsilonS neckShorteningEpsilon)
  refine ⟨epsilon₀, lt_min hRpos (lt_min hSpos neckShorteningEpsilon_pos),
    (min_le_left _ _).trans hRthreshold, ?_⟩
  intro M _ _ _ _ _ _ _ g D T hsmall C Q A η a b hcap hQ hab hη hηU hηa hηb hηL hz hy
  have hsmallR : T.tube.epsilon ≤ epsilonR := hsmall.trans (min_le_left _ _)
  have hsmallS : T.tube.epsilon ≤ epsilonS :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hshort : T.tube.epsilon ≤ neckShorteningEpsilon :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [T.tube.carrier_eq_chain_union] at hηb
  obtain ⟨j, hpj⟩ := mem_iUnion.mp hηb
  have hNj : (T.tube.chain.neck j.val).carrier ⊆ T.tube.carrier := by
    rw [T.tube.carrier_eq_chain_union]
    exact subset_iUnion_of_subset j Subset.rfl
  have hjepsilon := T.tube.chain.epsilon_eq j.val j.property
  have hdisj := (hseparation M g D C Q (η a) (η b) hQ hz hy).2.1
    T.cap (T.tube.chain.neck j.val) hcap (hjepsilon.trans_le hsmallS) hηa hpj
  obtain ⟨c, hc, _, _, _, hlow, _, _, hbackward⟩ :=
    exists_cap_endpoint_recentering T.cap D T.tube.epsilon_pos hcap hQ hηa (Or.inl hz)
  obtain ⟨α, hα0, hα1, hα, hαCap, hαL⟩ := hbackward
  obtain ⟨_, _, hsourceHigh, _, _, hhigh, hforward, _⟩ :=
    hrecentering T.tube.epsilon C T.tube.epsilon_pos hsmallR M g D
      (T.tube.chain.neck j.val) Q (η b) hQ hjepsilon hpj (Or.inr hy)
  obtain ⟨β, hβ0, hβ1, hβ, hβN, hβL⟩ := hforward
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσL⟩ :=
    exists_recentered_competitor_of_connectors g T.tube.epsilon_pos hQ hab hη hηU hηL
      hα0 hα1 hα (fun t ht => T.cap_subset (hαCap ht)) hαL
      hβ0 hβ1 hβ (fun t ht => T.tube_subset (hNj (hβN ht))) hβL
  obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγmin, hγfinite, hγL⟩ :=
    T.exists_core_neck_minimizer (T.tube.chain.neck j.val) hNj
      (T.tube.central_sphere_isotopy j.val j.property) hdisj
      (hjepsilon.trans_le hshort) zero_le_one hσ hσU
      (hσ0 ▸ T.cap.core_subset_carrier_m28 hc)
      (hσ1 ▸ (T.tube.chain.neck j.val).center_on_central_sphere) hσL
  refine ⟨c, hc, j.val, j.property, γ, hγ0.trans hσ0, hγ1.trans hσ1,
    ?_, ?_, ?_, hγ, hγU, ?_, hγfinite, hγL⟩
  · simpa only [hγ0, hσ0] using hlow hz
  · simpa only [hγ1, hσ1] using hhigh hy
  · simpa only [hγ1, hσ1] using hsourceHigh
  · simpa only [hγ0, hγ1] using hγmin

end PoincareConjecture.M28
