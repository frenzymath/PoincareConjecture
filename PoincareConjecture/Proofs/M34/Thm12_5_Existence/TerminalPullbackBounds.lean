import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalCurvatureBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S) (P : RicciFlowCurvatureTheory.{0})
  (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)




theorem closedFlow_compactPullback_spatialJet_bounds
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ j ≤ m, ∀ {U : Set StandardCapSpace}, IsOpen U →
      ∀ {e : StandardCapSpace → StandardCapSpace}, ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U →
      (∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) →
      (∀ x ∈ U, ∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v)) →
      ∀ t ∈ Icc 0 S, ∀ x ∈ K, x ∈ U →
        ‖iteratedFDeriv ℝ j
          (((L.closedFlow P E0 hS hSF hB hfull).metric t).pullbackCoefficients e) x‖ ≤ G := by
  obtain ⟨G, hG, hbound⟩ := partialFlow_compactPullback_spatialJet_bounds
    P E0 F hS hSF hB hfull hK m
  refine ⟨G, hG, ?_⟩
  intro j hj U hU e he hinv hmetric t ht x hx hxU
  let H := L.closedFlow P E0 hS hSF hB hfull
  have hold (s : ℝ) (hs : s ∈ Ico 0 S) :
      ‖iteratedFDeriv ℝ j ((H.metric s).pullbackCoefficients e) x‖ ≤ G := by
    have heq : H.metric s = F.flow.metric s :=
      L.closedMetric_of_lt P E0 hS hSF hB hfull hs.2
    rw [heq]
    exact hbound j hj hU he hinv hmetric s hs x hx hxU
  rcases ht.2.eq_or_lt with heq | hlt
  · subst t
    have hcoeff := H.smooth.contDiffOn_spacetime_pullbackCoefficients hU he
    have hjoint := hcoeff.iteratedFDeriv_snd_of_isOpen hU j
    have hc : ContinuousOn
        (fun s => ‖iteratedFDeriv ℝ j ((H.metric s).pullbackCoefficients e) x‖)
        (Icc 0 S) := by
      apply hjoint.continuousOn.norm.comp (continuous_id.prodMk continuous_const).continuousOn
      exact fun _ hs => ⟨hs, hxU⟩
    have hleft : Tendsto (fun s : ℝ => s) (𝓝[<] S) (𝓝[Icc 0 S] S) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [Ico_mem_nhdsLT hS] with s hs
      exact ⟨hs.1, hs.2.le⟩
    apply le_of_tendsto ((hc S ⟨hS.le, le_rfl⟩).tendsto.comp hleft)
    filter_upwards [Ico_mem_nhdsLT hS] with s hs
    exact hold s hs
  · exact hold t ⟨ht.1, hlt⟩



theorem metric_compactPullback_spatialJet_bounds
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ j ≤ m, ∀ {U : Set StandardCapSpace}, IsOpen U →
      ∀ {e : StandardCapSpace → StandardCapSpace}, ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U →
      (∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) →
      (∀ x ∈ U, ∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v)) →
      ∀ x ∈ K, x ∈ U → ‖iteratedFDeriv ℝ j
        ((L.metric P E0 hS hSF hB hfull).pullbackCoefficients e) x‖ ≤ G := by
  obtain ⟨G, hG, hbound⟩ := L.closedFlow_compactPullback_spatialJet_bounds
    P E0 hS hSF hB hfull hK m
  refine ⟨G, hG, ?_⟩
  intro j hj U hU e he hinv hmetric x hx hxU
  have h := hbound j hj hU he hinv hmetric S ⟨hS.le, le_rfl⟩ x hx hxU
  change ‖iteratedFDeriv ℝ j
    ((L.closedMetric P E0 hS hSF hB hfull S).pullbackCoefficients e) x‖ ≤ G at h
  rwa [L.closedMetric_terminal] at h



theorem metric_compactPullback_ellipticity
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ x ∈ K,
      ∀ e : StandardCapSpace → StandardCapSpace,
      (∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v)) →
      ∀ v : StandardCapSpace,
        a * ‖v‖ ^ 2 ≤ (L.metric P E0 hS hSF hB hfull).pullbackCoefficients e x v v ∧
          (L.metric P E0 hS hSF hB hfull).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2 := by
  obtain ⟨a, b, ha, hb, hbound⟩ := partialFlow_compactPullback_ellipticity P F hSF hB.le hfull hK
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx e he v
  have hlim := L.coefficients_apply_tendsto (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v)
  have hineq : ∀ᶠ t in 𝓝[<] S,
      a * ‖v‖ ^ 2 ≤ (F.flow.metric t).pullbackCoefficients e x v v ∧
        (F.flow.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2 := by
    filter_upwards [Ico_mem_nhdsLT hS] with t ht
    exact hbound t ht x hx e he v
  exact ⟨ge_of_tendsto hlim (hineq.mono fun _ h => h.1),
    le_of_tendsto hlim (hineq.mono fun _ h => h.2)⟩

end PoincareConjecture.M34.PartialFlowTerminalJets
