import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CanonicalSourceMinimizer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.Claim10_4SourceCover

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

structure CounterexampleSourceRegion {epsilon C A D₀ D : ℝ}
    (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
    (γ : ℝ → (E.flow.slice E.time).carrier) where
  cover : ConnectedNeckCapCover (E.flow.metric E.time)
  cover_epsilon : cover.epsilon = epsilon
  cover_constant : cover.cap_constant = C
  component_base : (E.flow.slice E.time).carrier
  cover_set : cover.X = connectedComponentIn
    {p | 4 * E.flow.scalar ⟨E.time, E.basepoint⟩ < E.flow.scalar ⟨E.time, p⟩}
    component_base
  carrier : Set (E.flow.slice E.time).carrier
  carrier_open : IsOpen carrier
  cover_subset : cover.X ⊆ carrier
  carrier_subset : carrier ⊆ cover.canonicalCarrierUnion
  path_mem : MapsTo γ (Icc (0 : ℝ) 1) carrier
  minimizing : (E.flow.metric E.time).pathELength γ 0 1 =
    intrinsicEDist (E.flow.metric E.time) carrier (γ 0) (γ 1)
  finite_length : (E.flow.metric E.time).pathELength γ 0 1 ≠ ⊤
  lower_scalar : E.flow.scalar ⟨E.time, γ 0⟩ ≤
    8 * (max C 2) * E.flow.scalar ⟨E.time, E.basepoint⟩
  upper_scalar : 32 * (max C 2) ^ 3 * E.flow.scalar ⟨E.time, E.basepoint⟩ <
    E.flow.scalar ⟨E.time, γ 1⟩

theorem exists_counterexample_source_necks_accuracy
    (P : RicciFlowCurvatureTheory.{u}) (T : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (epsilon C A D₀ D : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ →
        0 < C → 0 < D₀ → 32 * (max C 2) ^ 4 ≤ D →
        ∀ E : SameTimeCounterexample.{u} epsilon C A D₀ D,
          let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
          ∃ γ : ℝ → (E.flow.slice E.time).carrier,
            ∃ R : CounterexampleSourceRegion E γ, ∃ s t : ℝ,
            0 < s ∧ s < t ∧ t < 1 ∧
            ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
            (E.flow.metric E.time).pathELength γ s t <
              ENNReal.ofReal ((A + 2 * endpointConnectorBudget epsilon C) *
                Q ^ (-1 / 2 : ℝ)) ∧
            E.flow.scalar ⟨E.time, γ s⟩ = 16 * (max C 2) ^ 2 * Q ∧
            D * Q < 2 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, γ t⟩ ∧
            E.flow.scalar ⟨E.time, γ t⟩ = E.flow.scalar ⟨E.time, γ 1⟩ / (2 * max C 2) ∧
            (∀ v ∈ Icc s t, E.flow.scalar ⟨E.time, γ v⟩ ∈
              Icc (16 * (max C 2) ^ 2 * Q) (E.flow.scalar ⟨E.time, γ t⟩)) ∧
            ∃ hhalf : epsilon < 1 / 2, ∃ K : NeckOnlyCover (E.flow.metric E.time),
              K.X = γ '' Icc s t ∧ K.epsilon = epsilon ∧
              K.X ⊆ R.cover.X ∧
              (∀ N ∈ K.necks, ∃ J : GeneralizedStrongNeck E.flow E.time epsilon,
                N = strongNeck_top J hhalf ∧ J.center ∈ K.X) ∧
              ∀ v ∈ Icc s t, ∃ J : GeneralizedStrongNeck E.flow E.time epsilon,
                J.center = γ v := by
  obtain ⟨epsilonH, hHpos, hHthreshold, hcover⟩ :=
    exists_counterexample_superlevel_cover_accuracy P
  obtain ⟨epsilonU, hUpos, _, hminimum⟩ := exists_canonical_source_minimizer_accuracy T
  obtain ⟨epsilonN, hNpos, _, hnecks⟩ := exists_claim10_4_source_necks_accuracy P
  let epsilon₀ := min epsilonH (min epsilonU epsilonN)
  refine ⟨epsilon₀, lt_min hHpos (lt_min hUpos hNpos),
    (min_le_left _ _).trans hHthreshold, ?_⟩
  intro epsilon C A D₀ D hepsilon hsmall hC hD₀ hD E
  dsimp only
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  have hQ : 0 < Q := lt_of_lt_of_le hD₀ E.base_lower
  have hsmallH : epsilon ≤ epsilonH := hsmall.trans (min_le_left _ _)
  have hsmallU : epsilon ≤ epsilonU :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallN : epsilon ≤ epsilonN :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hB : 1 ≤ max C 2 := le_trans (by norm_num) (le_max_right C 2)
  have hD2 : 32 * (max C 2) ^ 2 ≤ D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by norm_num : 2 ≤ 4))
      (by norm_num : (0 : ℝ) ≤ 32)).trans hD
  obtain ⟨S, c, H, _, hc, hlevel, hHX, hHepsilon, hHC, hsource, hsourceL, _⟩ :=
    hcover epsilon C A D₀ D hepsilon hsmallH hC hD₀ hD2 E
  have hlarge : D * Q < E.flow.scalar ⟨E.time, S.path 1⟩ := by
    simpa only [Q, S.path_one] using E.scalar_large
  have hy : 32 * (max H.cap_constant 2) ^ 4 * Q <
      (E.flow.connection E.time).scalarCurvature (S.path 1) := by
    rw [hHC]
    exact (mul_le_mul_of_nonneg_right hD hQ.le).trans_lt hlarge
  obtain ⟨U, hUopen, hXU, hUV, γ, hlo, hhi, hcompare, hγ, hγU, hmin, hfinite, hlength⟩ :=
    hminimum (E.flow.slice E.time).carrier (E.flow.metric E.time)
      (E.flow.connection E.time) H (by simpa only [hHepsilon] using hsmallU)
      Q A S.path c 1 hQ hc.le S.path_smooth.contMDiffOn hsource hsourceL hlevel hy
  rw [hHC] at hlo hhi hcompare
  rw [hHepsilon, hHC] at hlength
  obtain ⟨s, t, h0s, hst, ht1, hsvalue, htvalue, hband, hsublength,
      hhalf, K, hKX, hKepsilon, hKsubset, hprovenance, hcenters⟩ :=
    hnecks E.flow E.time epsilon C Q hepsilon hsmallN hC hQ H hHepsilon hHC
      (S.path c) U γ 0 1 zero_le_one hHX hXU hUV hγ hγU hfinite hmin hlo hhi E.canonical
  have hBpos : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hdenom : 2 * max C 2 ≠ 0 := ne_of_gt (mul_pos (by norm_num) hBpos)
  have hhigh_eq : E.flow.scalar ⟨E.time, γ t⟩ * (2 * max C 2) =
      E.flow.scalar ⟨E.time, γ 1⟩ := by
    rw [htvalue]
    exact div_mul_cancel₀ _ hdenom
  have hretained : D * Q < 2 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, γ t⟩ := by
    calc
      D * Q < E.flow.scalar ⟨E.time, S.path 1⟩ := hlarge
      _ ≤ max C 2 * E.flow.scalar ⟨E.time, γ 1⟩ := hcompare
      _ = 2 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, γ t⟩ := by
        rw [← hhigh_eq]
        ring
  let R : CounterexampleSourceRegion E γ := {
    cover := H
    cover_epsilon := hHepsilon
    cover_constant := hHC
    component_base := S.path c
    cover_set := hHX
    carrier := U
    carrier_open := hUopen
    cover_subset := hXU
    carrier_subset := hUV
    path_mem := hγU
    minimizing := hmin
    finite_length := hfinite
    lower_scalar := hlo
    upper_scalar := hhi }
  refine ⟨γ, R, s, t, h0s, hst, ht1, hγ, hsublength.trans_lt hlength,
    hsvalue, hretained, htvalue, ?_, hhalf, K, hKX, hKepsilon, hKsubset,
    hprovenance, hcenters⟩
  intro v hv
  rw [htvalue]
  exact hband v hv

end PoincareConjecture.M28
