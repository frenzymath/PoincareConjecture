import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.RegularCanonical
import PoincareConjecture.Proofs.M32.Claim11_34.SliceCurvatureComparison
import PoincareConjecture.Proofs.M32.Claim11_35.SliceCapExclusion
import PoincareConjecture.Proofs.M32.Claim11_35.SliceComponentExclusion
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space




theorem exists_terminalBlowupConvergence_regular_slice_necks :
    ∃ epsilonRegular : ℝ, 0 < epsilonRegular ∧ epsilonRegular ≤ 1 / 200 ∧
      ∀ {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
        [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
        [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
        [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
        [∀ k, SecondCountableTopology (M k)]
        {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
        (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
        (Q : ∀ k, SingularLimitConclusion (H k))
        (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
        (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
        (hdiv : Tendsto (fun k =>
          ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)
        {J : Set ℝ} (G : GeneralizedBlowupConvergence
          (terminalBlowupSequence H Q x hpos hdiv) J) {a : ℝ},
        a ∈ J → a < 0 → ∀ {Kcut Ccap : ℝ}, 0 < Kcut → 0 < Ccap →
        (∀ k, (H k).r₀⁻¹ ^ 2 < Kcut) → (∀ k, (H k).constant ≤ Ccap) →
        (∀ k, (H k).epsilon ≤ epsilonRegular) →
        (∀ k, T k + a / (terminalBlowupSequence H Q x hpos hdiv).scale k ∉
          (H k).singularTimes) →
      ∀ {C : Type v} [TopologicalSpace C] [T2Space C] [ConnectedSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
        (gC : RiemannianMetric 2 C)
        (Phi : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.carrier.carrier),
        (∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (G.limit.flow.metric a).inner (Phi z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z w) =
            gC.inner z.1 v.1 w.1 + v.2 * w.2) →
      ∀ {K : Set G.limit.carrier.carrier}, IsCompact K →
        (∀ z ∈ K, 0 < (G.limit.flow.connection a).scalarCurvature z) →
        ∀ᶠ k in atTop, ∃ hak : a ∈ Icc (-G.exhaustion.time k) 0,
          K ⊆ G.exhaustion.space k ∧ ∀ z ∈ K,
            ∃ N : GeneralizedStrongNeck
              ((terminalBlowupSequence H Q x hpos hdiv).flow (G.subsequence k))
              (((terminalBlowupSequence H Q x hpos hdiv).base (G.subsequence k)).1 +
                a / (terminalBlowupSequence H Q x hpos hdiv).scale (G.subsequence k))
              ((H (G.subsequence k)).epsilon),
              N.center = blowup_sliceEmbedding G k a hak z := by
  obtain ⟨epsilonCap, hCap, hCapSmall, hcap⟩ := exists_blowup_slice_cap_exclusion.{u, v}
  obtain ⟨epsilonComponent, hComponent, _hComponentSmall, hcomponent⟩ :=
    exists_blowup_slice_closed_component_exclusion.{u, v}
  refine ⟨min epsilonCap epsilonComponent, lt_min hCap hComponent,
    (min_le_left _ _).trans hCapSmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H Q x hpos hdiv J G a ha haNeg Kcut Ccap
    _hKcut hCcap hcutoff hconstant hepsilon hregular C _ _ _ _ _ gC Phi hproduct K hK hpositive
  let S := terminalBlowupSequence H Q x hpos hdiv
  have hf : ContinuousOn (G.limit.flow.connection a).scalarCurvature K :=
    (G.limit.flow.contMDiff_scalarCurvature a ha).continuous.continuousOn
  obtain ⟨b, hb, hbound⟩ := hK.exists_forall_le' hf hpositive
  let m := b / 2
  have hm : 0 < m := by dsimp [m]; positivity
  filter_upwards [hcap G ha gC Phi hproduct hK hpositive hCcap,
    hcomponent G ha Phi.toHomeomorph hK hpositive hCcap,
    blowup_eventually_sliceScalar_error G ha hK hm,
    (S.scalar_diverges.comp G.subsequence_strictMono.tendsto_atTop).eventually
      (eventually_ge_atTop (Kcut / m))] with k hc hcomp hs hscale
  change Kcut / m ≤ S.scale (G.subsequence k) at hscale
  obtain ⟨hak, hsource, hc⟩ := hc
  obtain ⟨_, _, hcomp⟩ := hcomp
  obtain ⟨_, _, hs⟩ := hs
  refine ⟨hak, hsource, ?_⟩
  intro z hz
  have hq : 0 < S.scale (G.subsequence k) := S.base_scalar_pos (G.subsequence k)
  have hscaled : m < (S.flow (G.subsequence k)).scalar
      ((G.embedding k).pointMap a hak z) / S.scale (G.subsequence k) := by
    have hb' : b = 2 * m := by dsimp [m]; ring
    linarith [(abs_lt.mp (hs z hz)).1, hbound z hz]
  have hsourceScalar : Kcut < (S.flow (G.subsequence k)).scalar
      ((G.embedding k).pointMap a hak z) := by
    have hKq : Kcut ≤ m * S.scale (G.subsequence k) := by
      have h := (div_le_iff₀ hm).mp hscale
      nlinarith
    have h := (lt_div_iff₀ hq).mp hscaled
    nlinarith
  have hpreterminal : T (G.subsequence k) + a / S.scale (G.subsequence k) <
      T (G.subsequence k) := by linarith [div_neg_of_neg_of_pos haNeg hq]
  have hcanonical := extension_canonical_control_of_regular_preterminal
    (H (G.subsequence k)) (Q (G.subsequence k)).extension hpreterminal
    (hregular (G.subsequence k)) (blowup_sliceEmbedding G k a hak z)
    ((hcutoff (G.subsequence k)).trans hsourceScalar).le
  cases hcanonical with
  | neck N hcenter => exact ⟨N, hcenter⟩
  | cap N heps hconstantN hconnection hcore =>
    exact (hc z hz N (heps.trans_le ((hepsilon _).trans (min_le_left _ _)))
      (hconstantN.trans (hconstant _)) hconnection hcore).elim
  | component N hcontains => exact ((hcomp z hz).1 _ (hconstant _) N hcontains).elim
  | round N hcontains =>
    exact ((hcomp z hz).2 _ ((hepsilon _).trans (min_le_right _ _)) N hcontains).elim

end PoincareConjecture.M32
